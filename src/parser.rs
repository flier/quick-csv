//! The module provides data structures for parsing CSV data.

use alloc::borrow::Cow;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use core::iter::IntoIterator;
use core::ops::{Deref, Range};
use core::str;

use crate::index::{Builder as IndexBuilder, Index, COMMA, QUOTE};

/// Parse CSV data into a `Parsed`.
pub fn parse(buf: &[u8]) -> Parsed {
    Parser::default().parse(buf)
}

/// A builder used to create `Parser` in various manners.
#[derive(Debug, Default)]
pub struct Builder {
    parser: Parser,
}

impl Builder {
    /// Build the `Parser`.
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

    /// The quotation byte.
    pub fn with_quote(mut self, quote: u8) -> Self {
        self.parser.quote = quote;
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

/// A `Parser` that parses the CSV input.
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
    /// Parses this input slice in CSV format.
    pub fn parse<'a>(&self, buf: &'a [u8]) -> Parsed<'a> {
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

        Parsed {
            inner: Rc::new(Inner {
                buf,
                index: index_builder.finalize(),
                comment: self.comment,
            }),
        }
    }
}

#[derive(Debug)]
struct Inner<'a> {
    buf: &'a [u8],
    index: Index,
    comment: Option<u8>,
}

/// Parsed input with index.
#[derive(Clone, Debug)]
pub struct Parsed<'a> {
    inner: Rc<Inner<'a>>,
}

impl<'a> AsRef<[u8]> for Parsed<'a> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.inner.buf
    }
}

impl<'a> Parsed<'a> {
    /// The index of records and fields.
    pub fn index(&self) -> &Index {
        &self.inner.index
    }

    /// An iterator over the lines of input.
    ///
    /// Lines are ended with either a newline (\n) or a carriage return with a line feed (\r\n).
    /// The final line ending is optional.
    pub fn lines(&self) -> Lines<'a> {
        Lines {
            inner: self.inner.clone(),
            line: 0,
            pos: 0,
        }
    }

    /// An iterator over the records of input.
    pub fn records(&self) -> Records<'a> {
        Records(self.lines())
    }
}

impl<'a> IntoIterator for Parsed<'a> {
    type Item = Record<'a>;
    type IntoIter = Records<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.records()
    }
}

/// An iterator over the records of input.
#[derive(Clone, Debug)]
pub struct Records<'a>(Lines<'a>);

impl<'a> Iterator for Records<'a> {
    type Item = Record<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(line) = self.0.next() {
            if line.is_record() {
                return Some(line.into_record());
            }
        }

        None
    }
}

/// An iterator over the lines of input.
#[derive(Clone, Debug)]
pub struct Lines<'a> {
    inner: Rc<Inner<'a>>,
    line: usize,
    pos: usize,
}

impl<'a> Lines<'a> {
    /// Returns the current line number.
    #[inline]
    pub fn line(&self) -> usize {
        self.line
    }

    /// Returns the current position.
    #[inline]
    pub fn position(&self) -> usize {
        self.pos
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = Line<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.inner.index.len {
            None
        } else {
            self.inner
                .index
                .next_line(self.pos..self.inner.index.len)
                .map(|span| {
                    self.pos = span.end + 1;
                    self.line += 1;

                    let line = Line {
                        inner: self.inner.clone(),
                        span,
                        line: self.line,
                    };

                    trace!(
                        "line #{} @ {:?}: {}",
                        line.line,
                        line.span,
                        line.to_str().unwrap()
                    );

                    line
                })
        }
    }
}

/// A record of input.
#[derive(Clone, Debug)]
pub struct Record<'a>(Line<'a>);

impl<'a> Deref for Record<'a> {
    type Target = Line<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> IntoIterator for Record<'a> {
    type Item = Field<'a>;
    type IntoIter = Fields<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.fields()
    }
}

impl<'a> Record<'a> {
    /// An iterator over the fields of record.
    #[inline]
    pub fn fields(&self) -> Fields<'a> {
        Fields {
            inner: self.0.inner.clone(),
            span: self.0.span.clone(),
            column: 0,
            pos: self.0.span.start,
        }
    }
}

/// A line of input.
#[derive(Clone, Debug)]
pub struct Line<'a> {
    inner: Rc<Inner<'a>>,
    span: Range<usize>,
    line: usize,
}

impl<'a> AsRef<[u8]> for Line<'a> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.inner.buf[self.span.start..self.span.end]
    }
}

impl<'a> Line<'a> {
    /// Returns the number of bytes in the line.
    #[inline]
    pub fn len(&self) -> usize {
        self.span.len()
    }

    /// Returns true if the line has a length of 0.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.span.len() == 0
    }

    /// Returns the line number.
    #[inline]
    pub fn line(&self) -> usize {
        self.line
    }

    /// Returns the span for the `Line`.
    #[inline]
    pub fn span(&self) -> Range<usize> {
        self.span.clone()
    }

    /// Returns true if this `Line` is a comment, and false if not.
    #[inline]
    pub fn is_comment(&self) -> bool {
        self.as_ref().first().cloned() == self.inner.comment
    }

    /// Yields a `&str` slice if the `Line` contains a comment.
    #[inline]
    pub fn to_comment(&self) -> Option<Result<&str, str::Utf8Error>> {
        if self.is_comment() {
            self.as_ref()
                .split_first()
                .map(|(_, comment)| str::from_utf8(comment))
        } else {
            None
        }
    }

    /// Returns true if this `Line` is a record, and false if not.
    #[inline]
    pub fn is_record(&self) -> bool {
        !self.is_empty() && !self.is_comment()
    }

    /// Yields a `Record` if the `Line` contains a record.
    #[inline]
    pub fn to_record(&self) -> Option<Record> {
        if self.is_record() {
            Some(Record(self.clone()))
        } else {
            None
        }
    }

    /// Converts a `Line` into a `Record`.
    #[inline]
    pub fn into_record(self) -> Record<'a> {
        Record(self)
    }

    /// Yields a `&str` slice if the `Line` contains valid UTF-8.
    #[inline]
    pub fn to_str(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.as_ref())
    }
}

/// An iterator over the fields of record.
#[derive(Clone, Debug)]
pub struct Fields<'a> {
    inner: Rc<Inner<'a>>,
    span: Range<usize>,
    column: usize,
    pos: usize,
}

impl<'a> Fields<'a> {
    /// Returns the current column number.
    #[inline]
    pub fn column(&self) -> usize {
        self.column
    }

    /// Returns the current position.
    #[inline]
    pub fn position(&self) -> usize {
        self.pos
    }
}

impl<'a> Iterator for Fields<'a> {
    type Item = Field<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.span.end {
            None
        } else {
            let span = self.inner.index.next_field(self.pos..self.span.end);

            self.pos = span.end + 1;
            self.column += 1;

            let field = Field {
                inner: self.inner.clone(),
                span,
                column: self.column,
            };

            trace!(
                "  field #{} @ {:?}: {}",
                field.column,
                field.span,
                field.to_str().unwrap()
            );

            Some(field)
        }
    }
}

/// The `Field` of `Record`.
#[derive(Clone, Debug)]
pub struct Field<'a> {
    inner: Rc<Inner<'a>>,
    span: Range<usize>,
    column: usize,
}

impl<'a> AsRef<[u8]> for Field<'a> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.inner.buf[self.span.start..self.span.end]
    }
}

impl<'a> Field<'a> {
    /// Returns the column number.
    #[inline]
    pub fn column(&self) -> usize {
        self.column
    }

    /// Returns the span for the `Field`.
    #[inline]
    pub fn span(&self) -> Range<usize> {
        self.span.clone()
    }

    /// Yields a `&str` slice if the `Field` contains valid UTF-8.
    #[inline]
    pub fn to_str(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.as_ref())
    }

    /// The unescaped data.
    #[inline]
    pub fn unescaped<T: Escaped<'a> + ?Sized>(&'a self) -> Result<T::Unescaped, T::Error> {
        T::unescape(self.inner.buf, &self.inner.index, self.span.clone())
    }

    /// Unescape the data with special encoding.
    #[cfg(feature = "codec")]
    pub fn unescape_string(
        &self,
        encoding: ::encoding::EncodingRef,
        trap: ::encoding::DecoderTrap,
    ) -> Result<String, ::encoding::CodecError> {
        unescape_string(
            self.inner.buf,
            &self.inner.index,
            self.span.clone(),
            encoding,
            trap,
        )
    }
}

/// Escaped field.
pub trait Escaped<'a> {
    /// The unescaped data.
    type Unescaped;
    /// The `Error` in unescaping.
    type Error;

    /// Unescape the data
    fn unescape(
        buf: &'a [u8],
        index: &Index,
        span: Range<usize>,
    ) -> Result<Self::Unescaped, Self::Error>;
}

impl<'a> Escaped<'a> for str {
    type Unescaped = Cow<'a, str>;
    type Error = str::Utf8Error;

    fn unescape(
        buf: &'a [u8],
        index: &Index,
        span: Range<usize>,
    ) -> Result<Cow<'a, str>, Self::Error> {
        unescape_str(buf, index, span)
    }
}

impl<'a> Escaped<'a> for [u8] {
    type Unescaped = Cow<'a, [u8]>;
    type Error = ();

    fn unescape(
        buf: &'a [u8],
        index: &Index,
        span: Range<usize>,
    ) -> Result<Cow<'a, [u8]>, Self::Error> {
        Ok(unescape_bytes(buf, index, span))
    }
}

fn unescape_bytes<'a>(buf: &'a [u8], index: &Index, mut span: Range<usize>) -> Cow<'a, [u8]> {
    debug_assert!(
        span.start < index.len && span.end <= index.len,
        "span={:?}, len={}",
        span,
        index.len
    );

    if span.len() > 1
        && !index.quotes.is_empty()
        && index.is_quote(span.start)
        && index.is_quote(span.end - 1)
    {
        span = span.start + 1..span.end - 1
    }

    let mut off = span.start;
    let mut v = vec![];

    while let Some(pos) = index.next_escape(off..span.end) {
        v.extend_from_slice(&buf[off..pos]);
        off = pos + 1;
        if span.end < off {
            break;
        }
    }

    if off == span.start {
        (&buf[span.clone()]).into()
    } else {
        v.extend_from_slice(&buf[off..span.end]);
        v.into()
    }
}

fn unescape_str<'a>(
    buf: &'a [u8],
    index: &Index,
    mut span: Range<usize>,
) -> Result<Cow<'a, str>, str::Utf8Error> {
    debug_assert!(
        span.start < index.len && span.end <= index.len,
        "span={:?}, len={}",
        span,
        index.len
    );

    if span.len() > 1
        && !index.quotes.is_empty()
        && index.is_quote(span.start)
        && index.is_quote(span.end - 1)
    {
        span = span.start + 1..span.end - 1
    }

    let mut off = span.start;
    let mut s = String::new();

    while let Some(pos) = index.next_escape(off..span.end) {
        s.push_str(str::from_utf8(&buf[off..pos])?);
        off = pos + 1;
        if span.end < off {
            break;
        }
    }

    if off == span.start {
        str::from_utf8(&buf[span.clone()]).map(|s| s.into())
    } else {
        s.push_str(str::from_utf8(&buf[off..span.end])?);
        Ok(s.into())
    }
}

#[cfg(feature = "codec")]
fn unescape_string(
    buf: &[u8],
    index: &Index,
    mut span: Range<usize>,
    encoding: ::encoding::EncodingRef,
    trap: ::encoding::DecoderTrap,
) -> Result<String, ::encoding::CodecError> {
    debug_assert!(
        span.start < index.len && span.end <= index.len,
        "span={:?}, len={}",
        span,
        index.len
    );

    if span.len() > 1
        && !index.quotes.is_empty()
        && index.is_quote(span.start)
        && index.is_quote(span.end - 1)
    {
        span = span.start + 1..span.end - 1
    }

    let mut off = span.start;
    let mut s = String::new();

    while let Some(pos) = index.next_escape(off..span.end) {
        s.push_str(
            &encoding
                .decode(&buf[off..pos], trap)
                .map_err(|s| ::encoding::CodecError {
                    upto: off as isize,
                    cause: s,
                })?,
        );
        off = pos + 1;
        if span.end < off {
            break;
        }
    }

    if off == span.start {
        encoding
            .decode(&buf[off..span.end], trap)
            .map_err(|s| ::encoding::CodecError {
                upto: off as isize,
                cause: s,
            })
    } else {
        s.push_str(&encoding.decode(&buf[off..span.end], trap).map_err(|s| {
            ::encoding::CodecError {
                upto: off as isize,
                cause: s,
            }
        })?);
        Ok(s)
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

        assert_eq!(
            parse(
                br#""aaa","b
bb","ccc"
zzz,yyy,xxx"#,
            )
            .records()
            .map(|record| record
                .fields()
                .map(|field| field.to_str().unwrap().to_owned())
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

        assert_eq!(
            parse(b"\r\n\r\naaa,bbb,ccc\r\nzzz,yyy,xxx\r\n")
                .records()
                .map(|record| record
                    .fields()
                    .map(|field| field.to_str().unwrap().to_owned())
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["aaa", "bbb", "ccc"], vec!["zzz", "yyy", "xxx"]]
        );
    }

    #[test]
    fn test_parse_double_quote() {
        let _ = pretty_env_logger::try_init();

        let csv = parse(br#""aaa","b""b""b","0123456789""0123456789""0123456789""0123456789""0123456789""0123456789""0123456789""0123456789""#);

        assert_eq!(
            csv.records()
                .flat_map(|record| record.fields()
                    .map(|field| field.unescaped::<[u8]>().unwrap().into_owned()))
                .collect::<Vec<_>>(),
            vec![&b"aaa"[..], &b"b\"b\"b"[..], &b"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789"[..]]
        );
        assert_eq!(
            csv.records()
                .flat_map(|record| record.fields()
                    .map(|field| field.unescaped::<str>().unwrap().into_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "b\"b\"b", "0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789\"0123456789"]
        );
    }

    #[test]
    fn test_parse_tsv() {
        let _ = pretty_env_logger::try_init();

        let parser = Builder::default().with_delimiter(b'\t').build();
        let parsed = parser.parse(b"aaa\tbbb\tccc\nzzz\tyyy\txxx");

        assert_eq!(
            parsed
                .records()
                .map(|record| record
                    .fields()
                    .map(|field| field.to_str().unwrap().to_owned())
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![vec!["aaa", "bbb", "ccc"], vec!["zzz", "yyy", "xxx"]]
        );
    }

    #[test]
    fn test_parse_comment() {
        let _ = pretty_env_logger::try_init();

        let parser = Builder::default().with_comment(b'#').build();
        let parsed = parser.parse(b"#some comment\naaa,bbb,ccc\nzzz,yyy,xxx");

        assert_eq!(
            parsed
                .lines()
                .map(|line| if let Some(comment) = line.to_comment() {
                    vec![comment.unwrap().to_owned()]
                } else {
                    line.into_record()
                        .fields()
                        .map(|field| field.to_str().unwrap().to_owned())
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
            parse(s)
                .records()
                .flat_map(|record| record
                    .fields()
                    .map(|field| field.unescaped::<str>().unwrap().into_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "b\"bb", "ccc", "zzz", "yyy", "xxx"]
        );

        assert_eq!(
            Builder::default()
                .without_double_quote()
                .build()
                .parse(s)
                .records()
                .flat_map(|record| record
                    .fields()
                    .map(|field| field.unescaped::<str>().unwrap().into_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "b\"\"bb", "ccc", "zzz", "yyy", "xxx"]
        );
    }

    #[test]
    fn test_parse_without_quoting() {
        let _ = pretty_env_logger::try_init();

        let s = b"aaa,\"b\nbb\",ccc\nzzz,yyy,xxx";

        assert_eq!(
            parse(s)
                .records()
                .flat_map(|record| record
                    .fields()
                    .map(|field| field.to_str().unwrap().to_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "\"b\nbb\"", "ccc", "zzz", "yyy", "xxx"]
        );

        assert_eq!(
            Builder::default()
                .without_quoting()
                .build()
                .parse(s)
                .records()
                .flat_map(|record| record
                    .fields()
                    .map(|field| field.to_str().unwrap().to_owned()))
                .collect::<Vec<_>>(),
            vec!["aaa", "\"b", "bb\"", "ccc", "zzz", "yyy", "xxx"]
        );
    }

    #[cfg(feature = "codec")]
    #[test]
    fn test_parse_str_with_codec() {
        use encoding::types::Encoding;

        let _ = pretty_env_logger::try_init();

        let s = encoding::all::GBK
            .encode("测试,你好,世界", encoding::EncoderTrap::Ignore)
            .unwrap();

        assert!(parse(s.as_slice())
            .records()
            .flat_map(|record| record
                .fields()
                .map(|field| field.to_str().map(|s| s.to_owned())))
            .collect::<Result<Vec<_>, str::Utf8Error>>()
            .is_err());

        assert_eq!(
            Parser::default()
                .parse(s.as_slice())
                .records()
                .flat_map(|record| record.fields().map(|field| field
                    .unescape_string(encoding::all::GBK, encoding::DecoderTrap::Ignore)))
                .collect::<Result<Vec<_>, encoding::CodecError>>()
                .map_err(|_| ())
                .unwrap(),
            vec!["测试", "你好", "世界"]
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_parse_files() {
        use std::fs;
        use std::path::Path;

        let _ = pretty_env_logger::try_init();

        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("data");

        for &(filename, records, fields) in &[
            ("smallpop-colon.csv", 14, 14),
            ("smallpop-no-headers.csv", 0, 0),
            ("smallpop.csv", 0, 0),
            ("strange.csv", 0, 0),
            ("uspop-latin1.csv", 0, 0),
            ("uspop-null.csv", 0, 0),
            ("uspop.csv", 0, 0),
            ("bench/game.csv", 100000, 600000),
            ("bench/gtfs-mbta-stop-times.csv", 0, 0),
            ("bench/nfl.csv", 0, 0),
            ("bench/worldcitiespop.csv", 0, 0),
        ] {
            let data = fs::read(dir.join(filename)).unwrap();

            trace!("read {} bytes from {}", data.len(), filename);

            assert_eq!(
                parse(data.as_slice())
                    .records()
                    .fold((0, 0), |(records, fields), record| (
                        records + 1,
                        fields + record.fields().count()
                    )),
                (records, fields),
                "{} should have {} records and {} fields",
                filename,
                records,
                fields
            );
        }
    }
}
