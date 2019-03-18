#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use core::ops::{Deref, DerefMut, Range};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::avx::*;

pub const COMMA: u8 = b',';
pub const QUOTE: u8 = b'"';
pub const CR: u8 = b'\r';
pub const LF: u8 = b'\n';

#[derive(Debug)]
pub struct Index {
    delimiters: Vec<u64>,
    quotes: Vec<u64>,
    terminators: Vec<u64>,
    len: usize,
}

impl Index {
    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = (capacity + 63) / 64;

        Index {
            delimiters: Vec::with_capacity(capacity),
            quotes: Vec::with_capacity(capacity),
            terminators: Vec::with_capacity(capacity),
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn clear(&mut self) {
        self.delimiters.clear();
        self.quotes.clear();
        self.terminators.clear();
    }

    pub fn line_at(&self, mut pos: usize) -> Option<Range<usize>> {
        trace!("line_at(pos = {}), len = {}", pos, self.len);

        if pos >= self.len {
            None
        } else {
            let start = pos / 64;
            let mut i = start;
            let mut b = self.terminators[i] >> (pos % 64);

            let r = (!b).trailing_zeros();
            if r > 0 {
                pos += r as usize;
                b >>= r;
            }

            if pos >= self.len {
                None
            } else {
                let mut len = 0;

                while b == 0 {
                    i += 1;

                    if i < self.terminators.len() {
                        len += 64;
                        b = self.terminators[i];
                    } else {
                        break;
                    }
                }

                if i < self.terminators.len() {
                    len += b.trailing_zeros() as usize;
                } else if i == start + 1 {
                    len += self.len - pos;
                } else {
                    len += self.len % 64;
                }

                Some(pos..pos + len)
            }
        }
    }
}

#[derive(Debug)]
pub struct IndexBuilder {
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

impl Default for IndexBuilder {
    fn default() -> Self {
        IndexBuilder::new()
    }
}

impl Deref for IndexBuilder {
    type Target = Index;

    fn deref(&self) -> &Self::Target {
        &self.index
    }
}

impl DerefMut for IndexBuilder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.index
    }
}

impl IndexBuilder {
    pub fn new() -> Self {
        IndexBuilder::with_capacity(16)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        IndexBuilder {
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

        if self.double_quote {
            self.build_structural_quote_bitmap();
        }

        self.build_structural_line_bitmap();

        trace!("build finished");

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
    fn build_structural_quote_bitmap(&mut self) {
        trace!(
            "build_structural_quote_bitmap with {} quotes",
            self.index.quotes.len()
        );

        let len = self.index.quotes.len();

        for i in 0..len - 1 {
            let dquote = ((self.index.quotes[i] >> 1) | self.index.quotes[i + 1] << 63)
                & self.index.quotes[i];
            self.index.quotes[i] &= !(dquote | dquote << 1);
        }

        let b = &mut self.index.quotes[len - 1];
        let dquote = (*b >> 1) & *b;
        *b &= !(dquote | dquote << 1);
    }

    #[inline]
    fn build_structural_line_bitmap(&mut self) {
        trace!(
            "build_structural_line_bitmap with {} terminators",
            self.index.terminators.len()
        );

        let mut quote_count = 0;

        for (i, b) in self.index.terminators.iter_mut().enumerate() {
            trace!(
                "i = {}, terminator = {:08x}, quote = {:08x}",
                i,
                b,
                self.index.quotes[i]
            );

            if *b == 0 {
                let quotes = self.index.quotes[i].count_ones();

                trace!("found {} quotes @ {:?}", quotes, i * 64..(i + 1) * 64);

                quote_count += quotes;
            } else {
                let mut w = *b;

                while w != 0 {
                    let n = w.trailing_zeros();

                    let quotes = self.index.quotes[i].wrapping_shl(64 - n).count_ones();

                    trace!(
                        "found {} quotes @ {:?}, w = {:x}",
                        quotes,
                        i * 64..i * 64 + n as usize,
                        w
                    );

                    quote_count += quotes;

                    w = w >> (n + 1);

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
        let mut b = IndexBuilder::default();

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
        let mut b = IndexBuilder::default();

        unsafe {
            b.build_structural_character_bitmap(
                br#"1997,Ford,E350,"Super, ""luxurious"""""" truck""#,
            );
        }

        assert_eq!(b.quotes, vec![0x40fc_0180_8000]);

        b.build_structural_quote_bitmap();

        assert_eq!(b.quotes, vec![0x4000_0000_8000]);

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
        let mut b = IndexBuilder::default();

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
}
