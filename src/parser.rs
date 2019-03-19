use alloc::borrow::Cow;
use core::ops::{Deref, Range};
use core::ptr::NonNull;
use core::str;

use csv_core::Terminator;

use crate::index::{Index, IndexBuilder, COMMA, QUOTE};

#[derive(Debug)]
pub struct Parser {
    /// The delimiter that separates fields.
    delimiter: u8,
    /// The terminator that separates records.
    term: Terminator,
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
            term: Terminator::CRLF,
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
        if let Terminator::Any(terminator) = self.term {
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

    pub fn as_str(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.as_ref())
    }

    #[inline]
    pub fn unescaped(&self) -> Cow<str> {
        self.line().unescape(&self.span)
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
            let span = self.lines().record_at(self.pos..self.span.end);
            self.column += 1;
            self.pos = span.end + 1;

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

    #[inline]
    fn unescape(&self, span: &Range<usize>) -> Cow<str> {
        self.lines()
            .unescape(self.span.start + span.start..self.span.start + span.end)
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

    fn next(&mut self) -> Option<Line<'a>> {
        if self.pos >= self.index.len {
            None
        } else if let Some(span) = self.index.line_at(self.pos) {
            trace!("found line @ {:?}", span);

            let pos = span.start;
            self.pos = span.end + 1;
            self.line += 1;

            Some(Line {
                lines: unsafe { NonNull::new_unchecked(self as *mut _) },
                span,
                line: self.line,
                column: 0,
                pos,
            })
        } else {
            None
        }
    }
}

impl<'a> Lines<'a> {
    #[inline]
    pub fn line(&self) -> usize {
        self.line
    }

    #[inline]
    fn unescape(&self, span: Range<usize>) -> Cow<str> {
        "".into()
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

        assert_eq!(
            parser
                .parse(
                    br#""aaa","b
bb","ccc"
zzz,yyy,xxx"#,
                )
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
}
