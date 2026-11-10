//! Indentation-aware source lexer. Columns count Unicode scalar values, starting at one.
use crate::model::{Diagnostic, Span};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Word(String),
    Integer(String),
    Text(String),
    Symbol(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn is(&self, value: &str) -> bool {
        matches!(&self.kind, TokenKind::Word(s) | TokenKind::Symbol(s) if s == value)
    }
}

#[derive(Clone, Debug)]
pub struct Line {
    pub depth: usize,
    pub tokens: Vec<Token>,
    pub span: Span,
}

pub fn tokenize(source: &str) -> Result<Vec<Line>, Vec<Diagnostic>> {
    let mut lines = Vec::new();
    let mut errors = Vec::new();
    for (index, original) in source.lines().enumerate() {
        if original.trim().is_empty() || original.trim_start().starts_with('#') {
            continue;
        }
        match lex_line(original, index + 1) {
            Ok(line) => lines.push(line),
            Err(error) => errors.push(error),
        }
    }
    if errors.is_empty() {
        Ok(lines)
    } else {
        Err(errors)
    }
}

fn lex_line(source: &str, number: usize) -> Result<Line, Diagnostic> {
    let chars: Vec<char> = source.chars().collect();
    let mut pos = 0;
    while chars.get(pos) == Some(&' ') {
        pos += 1;
    }
    let span = |column| Span {
        line: number,
        column,
    };
    if chars.get(pos) == Some(&'\t') {
        return Err(Diagnostic::new(
            span(pos + 1),
            "use spaces for indentation, not tabs",
        ));
    }
    if pos % 4 != 0 {
        return Err(Diagnostic::new(
            span(pos + 1),
            "indentation must be a multiple of four spaces",
        ));
    }
    let depth = pos / 4;
    let start = span(pos + 1);
    let mut tokens = Vec::new();
    while pos < chars.len() {
        let begin = pos;
        let c = chars[pos];
        if c == ' ' || c == '\t' {
            pos += 1;
            continue;
        }
        if c == '#' {
            break;
        }
        let kind = if c.is_ascii_alphabetic() || c == '_' {
            pos += 1;
            while chars
                .get(pos)
                .is_some_and(|c| c.is_ascii_alphanumeric() || *c == '_')
            {
                pos += 1;
            }
            TokenKind::Word(chars[begin..pos].iter().collect())
        } else if c.is_ascii_digit() {
            pos += 1;
            while chars.get(pos).is_some_and(char::is_ascii_digit) {
                pos += 1;
            }
            TokenKind::Integer(chars[begin..pos].iter().collect())
        } else if c == '"' {
            pos += 1;
            let mut value = String::new();
            let mut closed = false;
            while pos < chars.len() {
                let ch = chars[pos];
                pos += 1;
                if ch == '"' {
                    closed = true;
                    break;
                }
                if ch.is_control() {
                    return Err(Diagnostic::new(
                        span(pos),
                        "unescaped control character in text literal",
                    ));
                }
                if ch != '\\' {
                    value.push(ch);
                    continue;
                }
                let escaped = chars
                    .get(pos)
                    .copied()
                    .ok_or_else(|| Diagnostic::new(span(pos), "unterminated text escape"))?;
                pos += 1;
                match escaped {
                    '"' => value.push('"'),
                    '\\' => value.push('\\'),
                    '/' => value.push('/'),
                    'n' => value.push('\n'),
                    'r' => value.push('\r'),
                    't' => value.push('\t'),
                    'b' => value.push('\u{8}'),
                    'f' => value.push('\u{c}'),
                    'u' => {
                        let first = hex_quad(&chars, &mut pos).ok_or_else(|| {
                            Diagnostic::new(
                                span(pos + 1),
                                "expected four hexadecimal digits after \\u",
                            )
                        })?;
                        let codepoint = if (0xd800..=0xdbff).contains(&first) {
                            if chars.get(pos) != Some(&'\\') || chars.get(pos + 1) != Some(&'u') {
                                return Err(Diagnostic::new(
                                    span(pos + 1),
                                    "high Unicode surrogate requires a low surrogate escape",
                                ));
                            }
                            pos += 2;
                            let second = hex_quad(&chars, &mut pos).ok_or_else(|| {
                                Diagnostic::new(
                                    span(pos + 1),
                                    "invalid low Unicode surrogate escape",
                                )
                            })?;
                            if !(0xdc00..=0xdfff).contains(&second) {
                                return Err(Diagnostic::new(
                                    span(pos + 1),
                                    "expected low Unicode surrogate",
                                ));
                            }
                            0x10000 + ((first - 0xd800) << 10) + (second - 0xdc00)
                        } else {
                            first
                        };
                        let decoded = char::from_u32(codepoint).ok_or_else(|| {
                            Diagnostic::new(span(pos + 1), "invalid Unicode scalar value")
                        })?;
                        value.push(decoded);
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            span(pos),
                            format!("invalid text escape \\{escaped}"),
                        ))
                    }
                }
            }
            if !closed {
                return Err(Diagnostic::new(
                    span(begin + 1),
                    "unterminated text literal",
                ));
            }
            if value.contains('\0') {
                return Err(Diagnostic::new(
                    span(begin + 1),
                    "text literals cannot contain NUL bytes",
                ));
            }
            TokenKind::Text(value)
        } else {
            let pair = chars.get(pos + 1).map(|next| format!("{c}{next}"));
            if pair
                .as_deref()
                .is_some_and(|p| matches!(p, "==" | "!=" | "<=" | ">=" | "->"))
            {
                pos += 2;
                TokenKind::Symbol(pair.unwrap())
            } else if "()[]{};+*/%=:,<>-.".contains(c) {
                pos += 1;
                TokenKind::Symbol(c.to_string())
            } else {
                return Err(Diagnostic::new(
                    span(pos + 1),
                    format!("unexpected character {c:?}"),
                ));
            }
        };
        tokens.push(Token {
            kind,
            span: span(begin + 1),
        });
    }
    Ok(Line {
        depth,
        tokens,
        span: start,
    })
}

fn hex_quad(chars: &[char], pos: &mut usize) -> Option<u32> {
    let mut value = 0;
    for _ in 0..4 {
        value = value * 16 + chars.get(*pos)?.to_digit(16)?;
        *pos += 1;
    }
    Some(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unicode_comments_and_spans() {
        let lines = tokenize("# ignored\r\n    say \"țară # 🌌\" # comment\r\n").unwrap();
        assert_eq!(lines[0].depth, 1);
        assert_eq!(lines[0].tokens[0].span, Span { line: 2, column: 5 });
        assert_eq!(lines[0].tokens[1].kind, TokenKind::Text("țară # 🌌".into()));
    }

    #[test]
    fn escapes_and_surrogate_pairs() {
        let lines = tokenize(r#"say "a\n\t\"\\\u021b\ud83c\udf0c""#).unwrap();
        assert_eq!(
            lines[0].tokens[1].kind,
            TokenKind::Text("a\n\t\"\\ț🌌".into())
        );
    }

    #[test]
    fn rejects_bad_text_and_indentation() {
        for text in [
            "  say 1",
            "\tsay 1",
            r#"say "\q""#,
            r#"say "\u0000""#,
            r#"say "\ud800""#,
            "say \"unfinished",
        ] {
            assert!(tokenize(text).is_err(), "{text}");
        }
    }

    #[test]
    fn collects_lexical_errors() {
        let errors = tokenize("say @\nsay $\n").unwrap_err();
        assert_eq!(errors.len(), 2);
        assert_eq!(errors[1].span, Span { line: 2, column: 5 });
    }
    #[test]
    fn array_delimiters_and_type_separator_have_spans() {
        let lines = tokenize("say [1, 2][0]\ncraft f(a: [flag; 2]) -> [text; 1]:").unwrap();
        assert!(lines[0].tokens[1].is("["));
        assert_eq!(lines[0].tokens[1].span, Span { line: 1, column: 5 });
        assert!(lines[1].tokens.iter().any(|token| token.is(";")));
    }
}
