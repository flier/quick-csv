use alloc::borrow::Cow;
use core::ops::{Deref, Range};
use core::ptr::NonNull;
use core::str;

use crate::index::{Index, IndexBuilder, COMMA, QUOTE};

#[derive(Debug, Default)]
pub struct Builder {
    parser: Parser,
}

impl Builder {
    pub fn build(self) -> Parser {
        self.parser
    }

    /// The delimiter that separates fields.
    pub fn with_delimiter(mut self, delimiter: u8) -> Self {
        self.parser.delimiter = delimiter;
        self
    }

    /// The terminator that separates records.
    pub fn with_terminator(mut self, terminator: u8) -> Self {
        self.parser.terminator = Some(terminator);
        self
    }

    /// Whether to recognize escaped quotes.
    pub fn with_escape(mut self, escape: u8) -> Self {
        self.parser.escape = Some(escape);
        self
    }

    /// Whether to recognized doubled quotes.
    pub fn without_double_quote(mut self) -> Self {
        self.parser.double_quote = false;
        self
    }

    /// If enabled, lines beginning with this byte are ignored.
    pub fn with_comment(mut self, comment: u8) -> Self {
        self.parser.comment = Some(comment);
        self
    }

    /// If enabled (the default), then quotes are respected. When disabled,
    /// quotes are not treated specially.
    pub fn without_quoting(mut self) -> Self {
        self.parser.quoting = false;
        self
    }
}

#[derive(Debug)]
pub struct Parser {
    /// The delimiter that separates fields.
    delimiter: u8,
    /// The terminator that separates records.
    terminator: Option<u8>,
    /// The quotation byte.
    quote: u8,
    /// Whether to recognize escaped quotes.
    escape: Option<u8>,
    /// Whether to recognized doubled quotes.
    double_quote: bool,
    /// If enabled, lines beginning with this byte are ignored.
    comment: Option<u8>,
    /// If enabled (the default), then quotes are respected. When disabled,
    /// quotes are not treated specially.
    quoting: bool,
}

impl Default for Parser {
    fn default() -> Self {
        Parser {
            delimiter: COMMA,
            terminator: None,
            quote: QUOTE,
            escape: None,
            double_quote: true,
            comment: None,
            quoting: true,
        }
    }
}

impl Parser {
    pub fn parse<'a>(&self, buf: &'a [u8]) -> Lines<'a> {
        let mut index_builder = IndexBuilder::with_capacity(buf.len());

        if self.delimiter != COMMA {
            index_builder.with_delimiter(self.delimiter);
        }
        if let Some(terminator) = self.terminator {
            index_builder.with_terminator(terminator);
        }
        if !self.quoting {
            index_builder.without_quote();
        } else {
            if self.quote != QUOTE {
                index_builder.with_quote(self.quote);
            }
            if !self.double_quote {
                index_builder.without_double_quote();
            }
        }

        index_builder.build(buf);

        Lines {
            buf,
            index: index_builder.finalize(),
            comment: self.comment,
            line: 0,
            pos: 0,
        }
    }
}

pub struct Record<'a> {
    line: NonNull<Line<'a>>,
    span: Range<usize>,
    column: usize,
}

impl<'a> AsRef<[u8]> for Record<'a> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.line().lines().as_ref()[self.span.start..self.span.end]
    }
}

impl<'a> Record<'a> {
    #[inline]
    pub fn column(&self) -> usize {
        self.column
    }

    #[inline]
    pub fn line(&'a self) -> &'a Line<'a> {
        unsafe { self.line.as_ref() }
    }

    #[inline]
    pub fn as_str(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.as_ref())
    }

    #[inline]
    pub fn unescaped_str(&self) -> Result<Cow<str>, str::Utf8Error> {
        self.line().lines().unescape_utf8(self.span.clone())
    }
}

pub struct Line<'a> {
    lines: NonNull<Lines<'a>>,
    span: Range<usize>,
    line: usize,
    column: usize,
    pos: usize,
}

impl<'a> Iterator for Line<'a> {
    type Item = Record<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.span.end {
            None
        } else {
            let span = self.lines().index.next_record(self.pos..self.span.end);

            trace!("found record @ {:?}", span);

            self.pos = span.end + 1;
            self.column += 1;

            Some(Record {
                line: unsafe { NonNull::new_unchecked(self as *mut _) },
                span,
                column: self.column,
            })
        }
    }
}

impl<'a> AsRef<[u8]> for Line<'a> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.lines().as_ref()[self.span.start..self.span.end]
    }
}

impl<'a> Line<'a> {
    #[inline]
    pub fn lines(&'a self) -> &'a Lines<'a> {
        unsafe { self.lines.as_ref() }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.span.len() == 0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.span.len()
    }

    #[inline]
    pub fn line(&self) -> usize {
        self.line
    }

    #[inline]
    pub fn is_comment(&self) -> bool {
        self.as_ref().first().cloned() == self.lines().comment
    }

    #[inline]
    pub fn as_comment(&self) -> Option<Result<&str, str::Utf8Error>> {
        if self.is_comment() {
            self.as_ref()
                .split_first()
                .map(|(_, comment)| str::from_utf8(comment))
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.as_ref())
    }
}

pub struct Lines<'a> {
    buf: &'a [u8],
    index: Index,
    comment: Option<u8>,
    line: usize,
    pos: usize,
}

impl<'a> AsRef<[u8]> for Lines<'a> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.buf
    }
}

impl<'a> Deref for Lines<'a> {
    type Target = Index;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.index
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = Line<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.index.len {
            None
        } else {
            self.index.next_line(self.pos..self.index.len).map(|span| {
                trace!("found line @ {:?}", span);

                let pos = span.start;
                self.pos = span.end + 1;
                self.line += 1;

                Line {
                    lines: unsafe { NonNull::new_unchecked(self as *mut _) },
                    span,
                    line: self.line,
                    column: 0,
                    pos,
                }
            })
        }
    }
}

impl<'a> Lines<'a> {
    #[inline]
    pub fn line(&self) -> usize {
        self.line
    }

    #[inline]
    fn unescape_utf8(&self, mut span: Range<usize>) -> Result<Cow<str>, str::Utf8Error> {
        debug_assert!(
            span.start < self.index.len && span.end <= self.index.len,
            "span={:?}, len={}",
            span,
            self.index.len
        );

        if span.len() > 1
            && !self.index.quotes.is_empty()
            && self.index.is_quote(span.start)
            && self.index.is_quote(span.end - 1)
        {
            span = span.start + 1..span.end - 1
        }

        let mut off = span.start;
        let mut s = String::new();

        while let Some(pos) = self.index.next_escape(off..span.end) {
            s.push_str(str::from_utf8(&self.buf[off..pos])?);
            off = pos + 1;
            if span.end < off {
                break;
            }
        }

        if off == span.start {
            str::from_utf8(&self.buf[span.clone()]).map(|s| s.into())
        } else {
            s.push_str(str::from_utf8(&self.buf[off..span.end])?);
            Ok(s.into())
        }
    }
}

#[cfg(test)]
mod tests {
    cfg_if! {
        if #[cfg(not(feature = "std"))] {
            use alloc::borrow::ToOwned;
            use alloc::{vec, vec::Vec};
        }
    }

    use super::*;

    #[test]
    fn test_parse_lines() {
        let _ = pretty_env_logger::try_init();

        let parser = Parser::default();
        let lines = parser.parse(
            br#""aaa","b
bb","ccc"
zzz,yyy,xxx"#,
        );

        assert_eq!(
            lines
                .map(|line| line
                    .map(|record| record.as_str().unwrap().to_owned())
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![
                vec!["\"aaa\"", "\"b\nbb\"", "\"ccc\""],
                vec!["zzz", "yyy", "xxx"]
            ]
        );
    }

    #[test]
    fn test_parse_line_with_crlf() {
        let _ = pretty_env_logger::try_init();

        let parser = Parser::default();
        let lines = parser.parse(b"\r\n\r\naaa,bbb,ccc\r\nzzz,yyy,xxx\r\n");

        assert_eq!(
            lines
                .map(|line| line
                    .map(|record| record.as_str().unwrap().to_owned())
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["aaa", "bbb", "ccc"], vec!["zzz", "yyy", "xxx"]]
        );
    }

    #[test]
    fn test_parse_double_quote() {
        let _ = pretty_env_logger::try_init();

        let parser = Parser::default();
        let lines = parser.parse(
            br#""aaa","b""b""b","0123456789""0123456789""0123456789""0123456789""0123456789""0123456789""0123456789""0123456789""#,
        );

        assert_eq!(
            lines.index,
            Index {
                delimiters: vec![0x8020, 0],
                quotes: vec![0x0001_4051, 0x8000_0000_0001],
                terminators: vec![0, 0],
                escapes: Some(vec![0x8008_0080_0800_0900, 0x0008_0080_0800]),
                len: 112,
            }
        );

        assert_eq!(
            lines
                .map(|line| line
                    .map(|record| record.unescaped_str().unwrap().into_owned())
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["aaa", "b\"b\"b", "0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789"]]
        );
    }

    #[test]
    fn test_parse_tsv() {
        let _ = pretty_env_logger::try_init();

        let parser = Builder::default().with_delimiter(b'\t').build();
        let lines = parser.parse(b"aaa\tbbb\tccc\nzzz\tyyy\txxx");

        assert_eq!(
            lines
                .map(|line| line
                    .map(|record| record.as_str().unwrap().to_owned())
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["aaa", "bbb", "ccc"], vec!["zzz", "yyy", "xxx"]]
        );
    }

    #[test]
    fn test_parse_comment() {
        let _ = pretty_env_logger::try_init();

        let parser = Builder::default().with_comment(b'#').build();
        let lines = parser.parse(b"#some comment\naaa,bbb,ccc\nzzz,yyy,xxx");

        assert_eq!(
            lines
                .map(|line| if let Some(comment) = line.as_comment() {
                    vec![comment.unwrap().to_owned()]
                } else {
                    line.map(|record| record.as_str().unwrap().to_owned())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
            vec![
                vec!["some comment"],
                vec!["aaa", "bbb", "ccc"],
                vec!["zzz", "yyy", "xxx"]
            ]
        );
    }

    #[test]
    fn test_parse_without_double_quote() {
        let _ = pretty_env_logger::try_init();

        let s = b"aaa,b\"\"bb,ccc\nzzz,yyy,xxx";

        assert_eq!(
            Parser::default()
                .parse(s)
                .flat_map(|line| line.map(|record| record.unescaped_str().unwrap().into_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "b\"bb", "ccc", "zzz", "yyy", "xxx"]
        );

        assert_eq!(
            Builder::default()
                .without_double_quote()
                .build()
                .parse(s)
                .flat_map(|line| line.map(|record| record.unescaped_str().unwrap().into_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "b\"\"bb", "ccc", "zzz", "yyy", "xxx"]
        );
    }

    #[test]
    fn test_parse_without_quoting() {
        let _ = pretty_env_logger::try_init();

        let s = b"aaa,\"b\nbb\",ccc\nzzz,yyy,xxx";

        assert_eq!(
            Parser::default()
                .parse(s)
                .flat_map(|line| line.map(|record| record.as_str().unwrap().to_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "\"b\nbb\"", "ccc", "zzz", "yyy", "xxx"]
        );

        assert_eq!(
            Builder::default()
                .without_quoting()
                .build()
                .parse(s)
                .flat_map(|line| line.map(|record| record.as_str().unwrap().to_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "\"b", "bb\"", "ccc", "zzz", "yyy", "xxx"]
        );
    }
}
