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
    line: &'a Line<'a>,
    span: Range<usize>,
}

impl<'a> AsRef<[u8]> for Record<'a> {
    fn as_ref(&self) -> &[u8] {
        &self.line[self.span.start..self.span.end]
    }
}

impl<'a> Deref for Record<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a> Record<'a> {}

pub struct Line<'a> {
    lines: NonNull<Lines<'a>>,
    span: Range<usize>,
    line: usize,
}

impl<'a> Iterator for Line<'a> {
    type Item = Record<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

impl<'a> AsRef<[u8]> for Line<'a> {
    fn as_ref(&self) -> &[u8] {
        &self.lines()[self.span.start..self.span.end]
    }
}

impl<'a> Deref for Line<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a> Line<'a> {
    fn lines(&self) -> &Lines<'a> {
        unsafe { self.lines.as_ref() }
    }

    pub fn is_empty(&self) -> bool {
        self.span.len() == 0
    }

    pub fn len(&self) -> usize {
        self.span.len()
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn is_comment(&self) -> bool {
        self.first().cloned() == self.lines().comment
    }

    pub fn as_comment(&self) -> Option<Result<&str, str::Utf8Error>> {
        if self.is_comment() {
            self.split_first()
                .map(|(_, comment)| str::from_utf8(comment))
        } else {
            None
        }
    }
}

pub struct Lines<'a> {
    buf: &'a [u8],
    index: Index,
    comment: Option<u8>,
    line: usize,
    pos: usize,
}

impl<'a> Deref for Lines<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.buf
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = Line<'a>;

    fn next(&mut self) -> Option<Line<'a>> {
        if self.pos >= self.index.len() {
            None
        } else if let Some(span) = self.index.line_at(self.pos) {
            trace!("found line @ {:?}", span);

            self.pos += span.len() + 1;
            self.line += 1;

            Some(Line {
                lines: unsafe { NonNull::new_unchecked(self as *mut _) },
                span,
                line: self.line,
            })
        } else {
            None
        }
    }
}

impl<'a> Lines<'a> {
    pub fn line(&self) -> usize {
        self.line
    }

    pub fn position(&self) -> usize {
        self.pos
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "std"))]
    use alloc::borrow::ToOwned;
    #[cfg(not(feature = "std"))]
    use alloc::{vec, vec::Vec};

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
                .map(|line| unsafe { str::from_utf8_unchecked(line.as_ref()) }.to_owned())
                .collect::<Vec<_>>(),
            vec!["\"aaa\",\"b\nbb\",\"ccc\"", "zzz,yyy,xxx"]
        );
    }

    #[test]
    fn test_parse_line_with_crlf() {
        let _ = pretty_env_logger::try_init();

        let parser = Parser::default();

        assert_eq!(
            parser
                .parse(b"aaa,bbb,ccc\r\nzzz,yyy,xxx")
                .map(|line| unsafe { str::from_utf8_unchecked(line.as_ref()) }.to_owned())
                .collect::<Vec<_>>(),
            vec!["aaa,bbb,ccc", "zzz,yyy,xxx"]
        );
    }
}
