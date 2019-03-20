#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use core::ops::{Deref, DerefMut, Range};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::avx::*;

pub const COMMA: u8 = b',';
pub const QUOTE: u8 = b'"';
pub const CR: u8 = b'\r';
pub const LF: u8 = b'\n';

pub fn build(buf: &[u8]) -> Index {
    let mut b = Builder::default();

    b.build(buf);
    b.finalize()
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Default, PartialEq)]
pub struct Index {
    pub delimiters: Vec<u64>,
    pub quotes: Vec<u64>,
    pub terminators: Vec<u64>,
    pub escapes: Option<Vec<u64>>,
    pub len: usize,
}

impl Index {
    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = (capacity + 63) / 64;

        Index {
            delimiters: Vec::with_capacity(capacity),
            quotes: Vec::with_capacity(capacity),
            terminators: Vec::with_capacity(capacity),
            escapes: None,
            len: 0,
        }
    }

    pub fn clear(&mut self) {
        self.delimiters.clear();
        self.quotes.clear();
        self.terminators.clear();
        self.escapes = None;
        self.len = 0;
    }

    pub fn is_delimiter(&self, pos: usize) -> bool {
        debug_assert!(pos <= self.len, "pos={}, len={}", pos, self.len);

        (self.delimiters[pos / 64] & (1 << (pos % 64))) != 0
    }

    pub fn is_quote(&self, pos: usize) -> bool {
        debug_assert!(pos <= self.len, "pos={}, len={}", pos, self.len);

        (self.quotes[pos / 64] & (1 << (pos % 64))) != 0
    }

    pub fn is_terminator(&self, pos: usize) -> bool {
        debug_assert!(pos <= self.len, "pos={}, len={}", pos, self.len);

        (self.terminators[pos / 64] & (1 << (pos % 64))) != 0
    }

    pub fn next_line(&self, mut span: Range<usize>) -> Option<Range<usize>> {
        // skip the leading terminators
        while span.start < span.end && self.is_terminator(span.start) {
            span.start += 1
        }

        if span.start == span.end {
            None
        } else {
            loop {
                match self.next_occurred(&self.terminators, &span) {
                    Some(end) => {
                        if end == span.start {
                            span.start += 1;

                            if span.start >= span.end {
                                return None;
                            }
                        } else {
                            return Some(span.start..end);
                        }
                    }
                    None => {
                        return if span.start >= span.end {
                            None
                        } else {
                            Some(span)
                        };
                    }
                }
            }
        }
    }

    pub fn next_record(&self, span: Range<usize>) -> Range<usize> {
        let end = self
            .next_occurred(&self.delimiters, &span)
            .unwrap_or(span.end);

        span.start..end
    }

    pub fn next_escape(&self, span: Range<usize>) -> Option<usize> {
        self.escapes
            .as_ref()
            .and_then(|escapes| self.next_occurred(escapes, &span))
    }

    fn next_occurred(&self, index: &[u64], span: &Range<usize>) -> Option<usize> {
        debug_assert!(
            span.start < span.end && span.end <= index.len() * 64,
            "span={:?}, len={}",
            span,
            index.len() * 64
        );

        let start = span.start / 64;
        let end = span.end / 64;

        let len = if start == end {
            let b = (index[start] >> (span.start % 64)) & ((1 << (span.end % 64)) - 1);

            b.trailing_zeros() as usize
        } else {
            let mut b = index[start] >> (span.start % 64);
            let mut len = (64 - span.start % 64).min(b.trailing_zeros() as usize);
            let mut off = start;

            while b == 0 && off < end {
                off += 1;

                b = index[start];

                len += b.trailing_zeros() as usize;
            }

            if off == end && end < index.len() {
                b = index[end] & ((1 << (span.end % 64)) - 1);

                len += (span.end % 64).min(b.trailing_zeros() as usize)
            }

            len
        };

        if len < span.len() {
            Some(span.start + len)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct Builder {
    /// The delimiter that separates fields.
    delimiter: __m256i,
    /// The quotation byte.
    quote: Option<__m256i>,
    /// The terminator that separates records.
    terminator: Option<__m256i>,

    cr: __m256i,
    lf: __m256i,

    /// Whether to recognized doubled quotes.
    double_quote: bool,

    index: Index,
}

impl Default for Builder {
    fn default() -> Self {
        Builder::new()
    }
}

impl Deref for Builder {
    type Target = Index;

    fn deref(&self) -> &Self::Target {
        &self.index
    }
}

impl DerefMut for Builder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.index
    }
}

impl Builder {
    pub fn new() -> Self {
        Builder::with_capacity(16)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Builder {
            delimiter: unsafe { mm256i(COMMA as i8) },
            quote: Some(unsafe { mm256i(QUOTE as i8) }),
            terminator: None,
            cr: unsafe { mm256i(CR as i8) },
            lf: unsafe { mm256i(LF as i8) },
            double_quote: true,
            index: Index::with_capacity(capacity),
        }
    }

    pub fn with_delimiter(&mut self, delimiter: u8) -> &mut Self {
        self.delimiter = unsafe { mm256i(delimiter as i8) };
        self
    }
    pub fn with_quote(&mut self, quote: u8) -> &mut Self {
        self.quote = Some(unsafe { mm256i(quote as i8) });
        self
    }
    pub fn without_quote(&mut self) -> &mut Self {
        self.quote = None;
        self
    }
    pub fn with_terminator(&mut self, terminator: u8) -> &mut Self {
        self.terminator = Some(unsafe { mm256i(terminator as i8) });
        self
    }
    pub fn without_double_quote(&mut self) -> &mut Self {
        self.double_quote = false;
        self
    }

    pub fn finalize(self) -> Index {
        self.index
    }

    pub fn build(&mut self, buf: &[u8]) {
        trace!(
            "build index with {} bytes, indexed {} bytes",
            buf.len(),
            self.index.len
        );

        let len = (buf.len() + 63) / 64;

        if len > self.index.delimiters.len() {
            self.index.delimiters.reserve(len);
            self.index.quotes.reserve(len);
            self.index.terminators.reserve(len);
        }

        unsafe {
            self.build_structural_character_bitmap(buf);
        }

        if self.quote.is_some() {
            if self.double_quote {
                self.index.escapes = Some(self.build_structural_quote_bitmap());
            }

            self.build_structural_line_bitmap();
        }

        self.index.len += buf.len();
    }

    #[inline]
    unsafe fn build_structural_character_bitmap(&mut self, s: &[u8]) {
        let len = s.len();
        let mut pos = 0;

        while pos + 63 < len {
            let s1 = u8_to_m256i(s, pos);
            let s2 = u8_to_m256i(s, pos + 32);

            self.index
                .delimiters
                .push(mbitmap(&s1, &s2, &self.delimiter));
            if let Some(quote) = self.quote.as_ref() {
                self.index.quotes.push(mbitmap(&s1, &s2, quote));
            }
            if let Some(terminator) = self.terminator.as_ref() {
                self.index.terminators.push(mbitmap(&s1, &s2, terminator))
            } else {
                self.index
                    .terminators
                    .push(mbitmap(&s1, &s2, &self.cr) | mbitmap(&s1, &s2, &self.lf));
            }

            pos += 64;
        }

        if pos + 32 < len {
            let s1 = u8_to_m256i(s, pos);
            let s2 = u8_to_m256i_rest(s, pos + 32);

            self.index
                .delimiters
                .push(mbitmap(&s1, &s2, &self.delimiter));
            if let Some(quote) = self.quote.as_ref() {
                self.index.quotes.push(mbitmap(&s1, &s2, quote));
            }
            if let Some(terminator) = self.terminator.as_ref() {
                self.index.terminators.push(mbitmap(&s1, &s2, terminator))
            } else {
                self.index
                    .terminators
                    .push(mbitmap(&s1, &s2, &self.cr) | mbitmap(&s1, &s2, &self.lf));
            }
        } else if pos + 32 == len {
            let s1 = u8_to_m256i(s, pos);

            self.index
                .delimiters
                .push(mbitmap_partial(&s1, &self.delimiter));
            if let Some(quote) = self.quote.as_ref() {
                self.index.quotes.push(mbitmap_partial(&s1, quote));
            }
            if let Some(terminator) = self.terminator.as_ref() {
                self.index
                    .terminators
                    .push(mbitmap_partial(&s1, terminator))
            } else {
                self.index
                    .terminators
                    .push(mbitmap_partial(&s1, &self.cr) | mbitmap_partial(&s1, &self.lf));
            }
        } else if pos < len {
            let s1 = u8_to_m256i_rest(s, pos);

            self.index
                .delimiters
                .push(mbitmap_partial(&s1, &self.delimiter));
            if let Some(quote) = self.quote.as_ref() {
                self.index.quotes.push(mbitmap_partial(&s1, quote));
            }
            if let Some(terminator) = self.terminator.as_ref() {
                self.index
                    .terminators
                    .push(mbitmap_partial(&s1, terminator))
            } else {
                self.index
                    .terminators
                    .push(mbitmap_partial(&s1, &self.cr) | mbitmap_partial(&s1, &self.lf));
            }
        }
    }

    #[inline]
    fn build_structural_quote_bitmap(&mut self) -> Vec<u64> {
        trace!(
            "build_structural_quote_bitmap with {} quotes",
            self.index.quotes.len()
        );

        let len = self.index.quotes.len();
        let mut escapes = Vec::with_capacity(len);

        if len > 1 {
            for i in 0..len - 1 {
                let dquote = ((self.index.quotes[i] >> 1) | self.index.quotes[i + 1] << 63)
                    & self.index.quotes[i];
                self.index.quotes[i] &= !(dquote | dquote << 1);
                escapes.push(dquote);
            }
        }

        if let Some(b) = self.index.quotes.last_mut() {
            let dquote = (*b >> 1) & *b;
            *b &= !(dquote | dquote << 1);
            escapes.push(dquote);
        }

        escapes
    }

    #[inline]
    fn build_structural_line_bitmap(&mut self) {
        trace!(
            "build_structural_line_bitmap with {} terminators",
            self.index.terminators.len()
        );

        let mut quote_count = 0;

        for (i, b) in self.index.terminators.iter_mut().enumerate() {
            if *b == 0 {
                quote_count += self.index.quotes[i].count_ones();
            } else {
                let mut w = *b;

                while w != 0 {
                    let n = w.trailing_zeros();

                    quote_count += self.index.quotes[i].wrapping_shl(64 - n).count_ones();

                    w = if n == 63 {
                        0
                    } else {
                        (w >> (n + 1)) & ((1 << (n + 1)) - 1)
                    };

                    if (quote_count & 1) == 1 {
                        *b &= !(1 << n);
                    } else {
                        quote_count = 0;
                    }
                }
            }
        }
    }
}

#[inline(always)]
unsafe fn mbitmap(s1: &__m256i, s2: &__m256i, m: &__m256i) -> u64 {
    let i1 = _mm256_movemask_epi8(_mm256_cmpeq_epi8(*s1, *m));
    let i2 = _mm256_movemask_epi8(_mm256_cmpeq_epi8(*s2, *m));
    u64::from(i1 as u32) | (u64::from(i2 as u32) << 32)
}

#[inline(always)]
unsafe fn mbitmap_partial(s: &__m256i, m: &__m256i) -> u64 {
    u64::from(_mm256_movemask_epi8(_mm256_cmpeq_epi8(*s, *m)) as u32)
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "std"))]
    use alloc::vec;

    use super::*;

    #[test]
    fn test_build_structural_character_bitmap() {
        let mut b = Builder::default();

        unsafe {
            b.build_structural_character_bitmap(br#"1997,Ford,E350,"Super, ""luxurious"" truck""#);
        }

        assert_eq!(b.delimiters, vec![0x0000_0020_4210]);
        assert_eq!(b.quotes, vec![0x040c_0180_8000]);
        assert_eq!(b.terminators, vec![0]);

        b.clear();

        unsafe {
            b.build_structural_character_bitmap(
                br#""aaa","b
bb","ccc"
zzz,yyy,xxx"#,
            );
        }

        assert_eq!(b.delimiters, vec![0x0440_1020]);
        assert_eq!(b.quotes, vec![0x0002_2851]);
        assert_eq!(b.terminators, vec![0x0004_0100]);
    }

    #[test]
    fn test_build_structural_quote_bitmap() {
        let mut b = Builder::default();

        unsafe {
            b.build_structural_character_bitmap(
                br#"1997,Ford,E350,"Super, ""luxurious"""""" truck""#,
            );
        }

        assert_eq!(b.quotes, vec![0x40fc_0180_8000]);

        let escapes = b.build_structural_quote_bitmap();

        assert_eq!(b.quotes, vec![0x4000_0000_8000]);
        assert_eq!(escapes, vec![0x007c_0080_0000]);

        b.clear();

        unsafe {
            b.build_structural_character_bitmap(
                br#""aaa","b
bb","ccc"
zzz,yyy,xxx"#,
            );
        }

        assert_eq!(b.quotes, vec![0x0002_2851]);

        b.build_structural_quote_bitmap();

        assert_eq!(b.quotes, vec![0x0002_2851]);
    }

    #[test]
    fn test_build_structural_line_bitmap() {
        let mut b = Builder::default();

        unsafe {
            b.build_structural_character_bitmap(
                br#""aaa","b
bb","ccc"
zzz,yyy,xxx"#,
            );
        }

        assert_eq!(b.terminators, vec![0x0004_0100]);

        b.build_structural_line_bitmap();

        assert_eq!(b.terminators, vec![0x0004_0000]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde() {
        let index = build(b"aaa,bbb,ccc");
        let s = serde_json::to_string(&index).unwrap();

        assert_eq!(
            s,
            "{\"delimiters\":[136],\"quotes\":[0],\"terminators\":[0],\"escapes\":[0],\"len\":11}"
        );

        assert_eq!(serde_json::from_str::<Index>(&s).unwrap(), index);
    }
}
