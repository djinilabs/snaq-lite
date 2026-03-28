//! UTF-16 (LSP) <-> byte offset conversion helpers.

use snaq_lite_lang::Span;
use tower_lsp::lsp_types::{Position, Range};

fn line_start_offsets(source: &str) -> Vec<usize> {
    let mut starts = vec![0usize];
    for (idx, b) in source.bytes().enumerate() {
        if b == b'\n' {
            starts.push(idx + 1);
        }
    }
    starts
}

fn line_bounds(source: &str, starts: &[usize], line: usize) -> Option<(usize, usize)> {
    let start = *starts.get(line)?;
    let end = starts.get(line + 1).copied().unwrap_or(source.len());
    Some((start, end))
}

fn utf16_units(s: &str) -> u32 {
    s.encode_utf16().count() as u32
}

fn is_ident_char_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Convert an LSP position (UTF-16 line/character) to byte offset in `source`.
/// Returns `None` when `line` is out of bounds.
pub fn position_to_byte_offset(source: &str, position: Position) -> Option<usize> {
    let starts = line_start_offsets(source);
    let (line_start, line_end) = line_bounds(source, &starts, position.line as usize)?;
    let line_text = &source[line_start..line_end];
    let mut consumed_units = 0u32;
    let mut last_boundary = line_start;

    for (rel, ch) in line_text.char_indices() {
        let ch_units = ch.len_utf16() as u32;
        let ch_start = line_start + rel;
        if consumed_units + ch_units > position.character {
            return Some(ch_start);
        }
        consumed_units += ch_units;
        last_boundary = ch_start + ch.len_utf8();
        if consumed_units == position.character {
            return Some(last_boundary);
        }
    }

    Some(line_end.max(last_boundary))
}

/// Convert a byte offset into an LSP position (UTF-16 line/character).
pub fn byte_offset_to_position(source: &str, mut offset: usize) -> Position {
    offset = offset.min(source.len());
    while offset > 0 && !source.is_char_boundary(offset) {
        offset -= 1;
    }

    let starts = line_start_offsets(source);
    let mut line = 0usize;
    for (idx, start) in starts.iter().enumerate() {
        if *start > offset {
            break;
        }
        line = idx;
    }
    let line_start = starts[line];
    let col_utf16 = utf16_units(&source[line_start..offset]);

    Position {
        line: line as u32,
        character: col_utf16,
    }
}

pub fn span_to_range(span: &Span, source: &str) -> Range {
    let start = byte_offset_to_position(source, span.start);
    let end = byte_offset_to_position(source, span.end);
    Range { start, end }
}

pub fn range_to_span(source: &str, range: &Range) -> Option<Span> {
    let start = position_to_byte_offset(source, range.start)?;
    let end = position_to_byte_offset(source, range.end)?;
    Some(Span {
        start: start.min(end),
        end: end.max(start),
    })
}

pub fn find_identifier_at_offset(source: &str, offset: usize) -> Option<(usize, usize)> {
    if source.is_empty() {
        return None;
    }
    let mut at = offset.min(source.len());
    if at == source.len() && at > 0 {
        at -= 1;
    }

    while at > 0 && !source.is_char_boundary(at) {
        at -= 1;
    }

    let bytes = source.as_bytes();
    if at < bytes.len() && !is_ident_char_byte(bytes[at]) {
        if at == 0 || !is_ident_char_byte(bytes[at.saturating_sub(1)]) {
            return None;
        }
        at -= 1;
    }

    if at >= bytes.len() || !is_ident_char_byte(bytes[at]) {
        return None;
    }

    let mut start = at;
    while start > 0 && is_ident_char_byte(bytes[start - 1]) {
        start -= 1;
    }

    let mut end = at + 1;
    while end < bytes.len() && is_ident_char_byte(bytes[end]) {
        end += 1;
    }

    Some((start, end))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf16_roundtrip_ascii_unicode_emoji() {
        let source = "a\né汉🙂z\n";
        let points = [
            Position {
                line: 0,
                character: 0,
            },
            Position {
                line: 1,
                character: 0,
            },
            Position {
                line: 1,
                character: 1,
            },
            Position {
                line: 1,
                character: 2,
            },
            Position {
                line: 1,
                character: 4,
            },
            Position {
                line: 1,
                character: 5,
            },
        ];

        for p in points {
            let off = position_to_byte_offset(source, p).expect("position in bounds");
            let back = byte_offset_to_position(source, off);
            assert_eq!(back, p);
        }
    }

    #[test]
    fn span_range_roundtrip_multiline_unicode() {
        let source = "αβ\nhello🙂\nç";
        let span = Span { start: 2, end: 14 };
        let range = span_to_range(&span, source);
        let back = range_to_span(source, &range).expect("valid range");
        assert_eq!(back.start, span.start);
        assert_eq!(back.end, span.end);
    }

    #[test]
    fn find_identifier_at_offset_handles_boundaries() {
        let source = "foo + bar_baz";
        let (s1, e1) = find_identifier_at_offset(source, 1).expect("foo");
        assert_eq!(&source[s1..e1], "foo");
        let (s2, e2) = find_identifier_at_offset(source, source.len()).expect("bar_baz");
        assert_eq!(&source[s2..e2], "bar_baz");
        assert!(find_identifier_at_offset(source, 4).is_none());
    }
}
