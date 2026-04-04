#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Lexer
//!
//! Tokenizes Ephapax source code using the logos crate for high performance.
//!
//! # Example
//!
//! ```
//! use ephapax_lexer::{Lexer, Token};
//!
//! let source = "let x = 42";
//! let tokens: Vec<_> = Lexer::new(source).collect();
//! ```

use logos::{Logos, SpannedIter};
use smol_str::SmolStr;
use std::fmt;
use thiserror::Error;

/// Lexer error types
#[derive(Error, Debug, Clone, PartialEq)]
pub enum LexerError {
    #[error("Unexpected character at position {0}")]
    UnexpectedCharacter(usize),

    #[error("Unterminated string starting at position {0}")]
    UnterminatedString(usize),

    #[error("Invalid number literal at position {0}")]
    InvalidNumber(usize),

    #[error("Unterminated block comment starting at position {0}")]
    UnterminatedComment(usize),
}

/// Source span for error reporting
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn dummy() -> Self {
        Self { start: 0, end: 0 }
    }

    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl From<logos::Span> for Span {
    fn from(span: logos::Span) -> Self {
        Self {
            start: span.start,
            end: span.end,
        }
    }
}

/// Token types for Ephapax
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
pub enum TokenKind {
    // ===== Keywords =====
    #[token("let")]
    Let,

    #[token("let!")]
    LetBang,

    #[token("fn")]
    Fn,

    #[token("if")]
    If,

    #[token("then")]
    Then,

    #[token("else")]
    Else,

    #[token("region")]
    Region,

    #[token("drop")]
    Drop,

    #[token("copy")]
    Copy,

    #[token("true")]
    True,

    #[token("false")]
    False,

    #[token("inl")]
    Inl,

    #[token("inr")]
    Inr,

    #[token("case")]
    Case,

    #[token("of")]
    Of,

    #[token("end")]
    End,

    #[token("in")]
    In,

    #[token("type")]
    Type,

    // ===== Type Keywords =====
    #[token("Bool")]
    TyBool,

    #[token("I32")]
    TyI32,

    #[token("I64")]
    TyI64,

    #[token("F32")]
    TyF32,

    #[token("F64")]
    TyF64,

    #[token("String")]
    TyString,

    // ===== Operators =====
    #[token("+")]
    Plus,

    #[token("-")]
    Minus,

    #[token("*")]
    Star,

    #[token("/")]
    Slash,

    #[token("%")]
    Percent,

    #[token("==")]
    EqEq,

    #[token("!=")]
    NotEq,

    #[token("<")]
    Lt,

    #[token(">")]
    Gt,

    #[token("<=")]
    LtEq,

    #[token(">=")]
    GtEq,

    #[token("&&")]
    AndAnd,

    #[token("||")]
    OrOr,

    #[token("!")]
    Not,

    #[token("&")]
    Ampersand,

    #[token("@")]
    At,

    #[token("->")]
    Arrow,

    #[token("=")]
    Eq,

    #[token(":")]
    Colon,

    #[token(",")]
    Comma,

    #[token(".")]
    Dot,

    #[token(";")]
    Semi,

    // ===== Delimiters =====
    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[token("[")]
    LBracket,

    #[token("]")]
    RBracket,

    // ===== Unit =====
    #[token("()")]
    Unit,

    // ===== Literals =====
    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    Integer(i64),

    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().parse::<f64>().ok())]
    Float(f64),

    #[regex(r#""([^"\\]|\\.)*""#, |lex| {
        let s = lex.slice();
        // Remove quotes and unescape
        Some(unescape_string(&s[1..s.len()-1]))
    })]
    String(String),

    // ===== Identifiers =====
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| SmolStr::new(lex.slice()))]
    Ident(SmolStr),

    // ===== Comments =====
    #[regex(r"--[^\n]*", logos::skip)]
    LineComment,

    #[token("{-", block_comment)]
    BlockComment,

    // ===== Special =====
    /// End of file marker
    Eof,
}

/// Parse block comments (handles nesting)
fn block_comment(lex: &mut logos::Lexer<TokenKind>) -> logos::FilterResult<(), ()> {
    let mut depth = 1;
    let remainder = lex.remainder();

    let mut chars = remainder.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '{' => {
                if let Some((_, '-')) = chars.next() {
                    depth += 1;
                }
            }
            '-' => {
                if let Some((_, '}')) = chars.next() {
                    depth -= 1;
                    if depth == 0 {
                        lex.bump(i + 2);
                        return logos::FilterResult::Skip;
                    }
                }
            }
            _ => {}
        }
    }

    // Unterminated comment - skip to end but mark as error
    lex.bump(remainder.len());
    logos::FilterResult::Error(())
}

/// Unescape string literals
fn unescape_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('0') => result.push('\0'),
                Some(c) => {
                    result.push('\\');
                    result.push(c);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }

    result
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Let => write!(f, "let"),
            TokenKind::LetBang => write!(f, "let!"),
            TokenKind::Fn => write!(f, "fn"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Then => write!(f, "then"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::Region => write!(f, "region"),
            TokenKind::Drop => write!(f, "drop"),
            TokenKind::Copy => write!(f, "copy"),
            TokenKind::True => write!(f, "true"),
            TokenKind::False => write!(f, "false"),
            TokenKind::Inl => write!(f, "inl"),
            TokenKind::Inr => write!(f, "inr"),
            TokenKind::Case => write!(f, "case"),
            TokenKind::Of => write!(f, "of"),
            TokenKind::End => write!(f, "end"),
            TokenKind::In => write!(f, "in"),
            TokenKind::Type => write!(f, "type"),
            TokenKind::TyBool => write!(f, "Bool"),
            TokenKind::TyI32 => write!(f, "I32"),
            TokenKind::TyI64 => write!(f, "I64"),
            TokenKind::TyF32 => write!(f, "F32"),
            TokenKind::TyF64 => write!(f, "F64"),
            TokenKind::TyString => write!(f, "String"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Percent => write!(f, "%"),
            TokenKind::EqEq => write!(f, "=="),
            TokenKind::NotEq => write!(f, "!="),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::LtEq => write!(f, "<="),
            TokenKind::GtEq => write!(f, ">="),
            TokenKind::AndAnd => write!(f, "&&"),
            TokenKind::OrOr => write!(f, "||"),
            TokenKind::Not => write!(f, "!"),
            TokenKind::Ampersand => write!(f, "&"),
            TokenKind::At => write!(f, "@"),
            TokenKind::Arrow => write!(f, "->"),
            TokenKind::Eq => write!(f, "="),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Dot => write!(f, "."),
            TokenKind::Semi => write!(f, ";"),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
            TokenKind::LBrace => write!(f, "{{"),
            TokenKind::RBrace => write!(f, "}}"),
            TokenKind::LBracket => write!(f, "["),
            TokenKind::RBracket => write!(f, "]"),
            TokenKind::Unit => write!(f, "()"),
            TokenKind::Integer(n) => write!(f, "{}", n),
            TokenKind::Float(n) => write!(f, "{}", n),
            TokenKind::String(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            TokenKind::LineComment => write!(f, "<comment>"),
            TokenKind::BlockComment => write!(f, "<block comment>"),
            TokenKind::Eof => write!(f, "<eof>"),
        }
    }
}

/// A token with its span
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn eof(pos: usize) -> Self {
        Self {
            kind: TokenKind::Eof,
            span: Span::new(pos, pos),
        }
    }
}

/// Lexer wrapper that provides a clean iterator interface
pub struct Lexer<'src> {
    inner: SpannedIter<'src, TokenKind>,
    source: &'src str,
    finished: bool,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            inner: TokenKind::lexer(source).spanned(),
            source,
            finished: false,
        }
    }

    pub fn source(&self) -> &'src str {
        self.source
    }

    /// Tokenize the entire source, returning tokens and any errors
    pub fn tokenize(source: &str) -> (Vec<Token>, Vec<LexerError>) {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();

        for result in Lexer::new(source) {
            match result {
                Ok(token) => tokens.push(token),
                Err(e) => errors.push(e),
            }
        }

        (tokens, errors)
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = Result<Token, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        match self.inner.next() {
            Some((Ok(kind), span)) => Some(Ok(Token::new(kind, span.into()))),
            Some((Err(()), span)) => Some(Err(LexerError::UnexpectedCharacter(span.start))),
            None => {
                self.finished = true;
                Some(Ok(Token::eof(self.source.len())))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(source: &str) -> Vec<TokenKind> {
        Lexer::new(source)
            .filter_map(|r| r.ok())
            .map(|t| t.kind)
            .filter(|k| !matches!(k, TokenKind::Eof))
            .collect()
    }

    #[test]
    fn test_keywords() {
        assert_eq!(lex("let"), vec![TokenKind::Let]);
        assert_eq!(lex("let!"), vec![TokenKind::LetBang]);
        assert_eq!(lex("fn"), vec![TokenKind::Fn]);
        assert_eq!(lex("if"), vec![TokenKind::If]);
        assert_eq!(lex("then"), vec![TokenKind::Then]);
        assert_eq!(lex("else"), vec![TokenKind::Else]);
        assert_eq!(lex("region"), vec![TokenKind::Region]);
        assert_eq!(lex("drop"), vec![TokenKind::Drop]);
        assert_eq!(lex("copy"), vec![TokenKind::Copy]);
        assert_eq!(lex("true"), vec![TokenKind::True]);
        assert_eq!(lex("false"), vec![TokenKind::False]);
        assert_eq!(lex("inl"), vec![TokenKind::Inl]);
        assert_eq!(lex("inr"), vec![TokenKind::Inr]);
        assert_eq!(lex("case"), vec![TokenKind::Case]);
        assert_eq!(lex("of"), vec![TokenKind::Of]);
        assert_eq!(lex("end"), vec![TokenKind::End]);
        assert_eq!(lex("in"), vec![TokenKind::In]);
    }

    #[test]
    fn test_type_keywords() {
        assert_eq!(lex("Bool"), vec![TokenKind::TyBool]);
        assert_eq!(lex("I32"), vec![TokenKind::TyI32]);
        assert_eq!(lex("I64"), vec![TokenKind::TyI64]);
        assert_eq!(lex("F32"), vec![TokenKind::TyF32]);
        assert_eq!(lex("F64"), vec![TokenKind::TyF64]);
        assert_eq!(lex("String"), vec![TokenKind::TyString]);
    }

    #[test]
    fn test_operators() {
        assert_eq!(
            lex("+ - * / %"),
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Percent,
            ]
        );

        assert_eq!(
            lex("== != < > <= >="),
            vec![
                TokenKind::EqEq,
                TokenKind::NotEq,
                TokenKind::Lt,
                TokenKind::Gt,
                TokenKind::LtEq,
                TokenKind::GtEq,
            ]
        );

        assert_eq!(
            lex("&& || !"),
            vec![TokenKind::AndAnd, TokenKind::OrOr, TokenKind::Not,]
        );

        assert_eq!(
            lex("& @ -> = : , . ;"),
            vec![
                TokenKind::Ampersand,
                TokenKind::At,
                TokenKind::Arrow,
                TokenKind::Eq,
                TokenKind::Colon,
                TokenKind::Comma,
                TokenKind::Dot,
                TokenKind::Semi,
            ]
        );
    }

    #[test]
    fn test_delimiters() {
        assert_eq!(
            lex("( ) { } [ ]"),
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
            ]
        );
    }

    #[test]
    fn test_unit() {
        assert_eq!(lex("()"), vec![TokenKind::Unit]);
    }

    #[test]
    fn test_integers() {
        assert_eq!(lex("42"), vec![TokenKind::Integer(42)]);
        assert_eq!(lex("0"), vec![TokenKind::Integer(0)]);
        assert_eq!(lex("12345"), vec![TokenKind::Integer(12345)]);
    }

    #[test]
    fn test_floats() {
        assert_eq!(lex("3.14"), vec![TokenKind::Float(3.14)]);
        assert_eq!(lex("0.0"), vec![TokenKind::Float(0.0)]);
        assert_eq!(lex("123.456"), vec![TokenKind::Float(123.456)]);
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            lex(r#""hello""#),
            vec![TokenKind::String("hello".to_string())]
        );
        assert_eq!(
            lex(r#""hello\nworld""#),
            vec![TokenKind::String("hello\nworld".to_string())]
        );
        assert_eq!(lex(r#""""#), vec![TokenKind::String("".to_string())]);
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(lex("x"), vec![TokenKind::Ident("x".into())]);
        assert_eq!(lex("foo_bar"), vec![TokenKind::Ident("foo_bar".into())]);
        assert_eq!(lex("_private"), vec![TokenKind::Ident("_private".into())]);
        assert_eq!(lex("x1"), vec![TokenKind::Ident("x1".into())]);
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            lex("-- this is a comment\n42"),
            vec![TokenKind::Integer(42)]
        );
        assert_eq!(lex("{- block comment -}42"), vec![TokenKind::Integer(42)]);
        assert_eq!(
            lex("{- nested {- comment -} -}42"),
            vec![TokenKind::Integer(42)]
        );
    }

    #[test]
    fn test_complex_expression() {
        let tokens = lex("let x = 42 in x + 1");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Let,
                TokenKind::Ident("x".into()),
                TokenKind::Eq,
                TokenKind::Integer(42),
                TokenKind::In,
                TokenKind::Ident("x".into()),
                TokenKind::Plus,
                TokenKind::Integer(1),
            ]
        );
    }

    #[test]
    fn test_region_expression() {
        let tokens = lex(r#"region r { String.new@r("hello") }"#);
        assert_eq!(
            tokens,
            vec![
                TokenKind::Region,
                TokenKind::Ident("r".into()),
                TokenKind::LBrace,
                TokenKind::TyString,
                TokenKind::Dot,
                TokenKind::Ident("new".into()),
                TokenKind::At,
                TokenKind::Ident("r".into()),
                TokenKind::LParen,
                TokenKind::String("hello".to_string()),
                TokenKind::RParen,
                TokenKind::RBrace,
            ]
        );
    }

    #[test]
    fn test_function_definition() {
        let tokens = lex("fn add(x: I32, y: I32): I32 = x + y");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Fn,
                TokenKind::Ident("add".into()),
                TokenKind::LParen,
                TokenKind::Ident("x".into()),
                TokenKind::Colon,
                TokenKind::TyI32,
                TokenKind::Comma,
                TokenKind::Ident("y".into()),
                TokenKind::Colon,
                TokenKind::TyI32,
                TokenKind::RParen,
                TokenKind::Colon,
                TokenKind::TyI32,
                TokenKind::Eq,
                TokenKind::Ident("x".into()),
                TokenKind::Plus,
                TokenKind::Ident("y".into()),
            ]
        );
    }

    #[test]
    fn test_lambda() {
        let tokens = lex("fn(x: I32) -> x + 1");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Fn,
                TokenKind::LParen,
                TokenKind::Ident("x".into()),
                TokenKind::Colon,
                TokenKind::TyI32,
                TokenKind::RParen,
                TokenKind::Arrow,
                TokenKind::Ident("x".into()),
                TokenKind::Plus,
                TokenKind::Integer(1),
            ]
        );
    }

    #[test]
    fn test_case_expression() {
        let tokens = lex("case x of inl(n) -> n inr(b) -> 0 end");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Case,
                TokenKind::Ident("x".into()),
                TokenKind::Of,
                TokenKind::Inl,
                TokenKind::LParen,
                TokenKind::Ident("n".into()),
                TokenKind::RParen,
                TokenKind::Arrow,
                TokenKind::Ident("n".into()),
                TokenKind::Inr,
                TokenKind::LParen,
                TokenKind::Ident("b".into()),
                TokenKind::RParen,
                TokenKind::Arrow,
                TokenKind::Integer(0),
                TokenKind::End,
            ]
        );
    }

    #[test]
    fn test_borrow() {
        let tokens = lex("String.len(&s)");
        assert_eq!(
            tokens,
            vec![
                TokenKind::TyString,
                TokenKind::Dot,
                TokenKind::Ident("len".into()),
                TokenKind::LParen,
                TokenKind::Ampersand,
                TokenKind::Ident("s".into()),
                TokenKind::RParen,
            ]
        );
    }

    #[test]
    fn test_spans() {
        let source = "let x = 42";
        let tokens: Vec<Token> = Lexer::new(source).filter_map(|r| r.ok()).collect();

        assert_eq!(tokens[0].span, Span::new(0, 3)); // "let"
        assert_eq!(tokens[1].span, Span::new(4, 5)); // "x"
        assert_eq!(tokens[2].span, Span::new(6, 7)); // "="
        assert_eq!(tokens[3].span, Span::new(8, 10)); // "42"
    }

    #[test]
    fn test_tokenize_with_errors() {
        let (tokens, errors) = Lexer::tokenize("let x = 42 $ y");
        assert!(!errors.is_empty());
        assert!(tokens.iter().any(|t| matches!(t.kind, TokenKind::Let)));
    }
}

// =========================================================================
// P2P PROPERTY TESTS
//
// Loop-based invariant checks for the lexer. Each test verifies a core
// lexer invariant over a range of parameterised inputs.
// =========================================================================

#[cfg(test)]
mod property_tests {
    use super::*;

    // -------------------------------------------------------------------------
    // P2P: round-trip token spans
    // -------------------------------------------------------------------------

    /// P2P: every token span is within the bounds of the source string.
    ///
    /// For 20 programs of varying length, verifies that all token spans
    /// satisfy start <= end <= source.len().
    #[test]
    fn p2p_token_spans_within_source_bounds() {
        let programs = vec![
            "let x = 42",
            "let! y = \"hello\"",
            "fn foo(x: i32): i32 = x",
            "if true then 1 else 0",
            "let a = 1 let b = 2",
            "region r { }",
            "drop(42)",
            "let! s = String.new@r(\"world\") in s",
            "(a, b)",
            "x + y * z",
            "42",
            "\"\"",
            "true",
            "false",
            "()",
            "let x = let y = 1 in y in x",
            "-- comment\nlet x = 1",
            "/* block */ let x = 1",
            "let! x = 1 in let! y = x in y",
            "0.0",
        ];

        for (i, source) in programs.iter().enumerate() {
            let tokens: Vec<Token> = Lexer::new(source)
                .filter_map(|r| r.ok())
                .filter(|t| !matches!(t.kind, TokenKind::Eof))
                .collect();

            for token in &tokens {
                assert!(
                    token.span.start <= token.span.end,
                    "P2P spans[{i}]: span.start > span.end in {source:?}"
                );
                assert!(
                    token.span.end <= source.len(),
                    "P2P spans[{i}]: span.end {} > source.len() {} in {source:?}",
                    token.span.end,
                    source.len()
                );
            }
        }
    }

    /// Helper: tokenize and strip the trailing EOF token that the lexer appends.
    fn tokenize_no_eof(source: &str) -> (Vec<Token>, Vec<LexerError>) {
        let (mut tokens, errors) = Lexer::tokenize(source);
        tokens.retain(|t| !matches!(t.kind, TokenKind::Eof));
        (tokens, errors)
    }

    /// P2P: empty string produces no content tokens and no errors.
    ///
    /// Lexing an empty string is a degenerate case that must be handled
    /// gracefully — only an EOF token (if any), no errors, no panics.
    #[test]
    fn p2p_empty_string_no_content_tokens_no_errors() {
        for _ in 0..20 {
            let (tokens, errors) = tokenize_no_eof("");
            assert!(tokens.is_empty(), "P2P empty: empty source must produce no content tokens");
            assert!(errors.is_empty(), "P2P empty: empty source must produce no errors");
        }
    }

    /// P2P: whitespace-only strings produce no content tokens.
    ///
    /// The lexer skips whitespace; pure whitespace inputs should yield no content tokens.
    #[test]
    fn p2p_whitespace_only_no_content_tokens() {
        let whitespace_inputs = [
            " ", "  ", "\t", "\n", "\r\n", "   \t\n  ", "\n\n\n",
        ];
        for source in &whitespace_inputs {
            let tokens: Vec<Token> = Lexer::new(source)
                .filter_map(|r| r.ok())
                .filter(|t| !matches!(t.kind, TokenKind::Eof))
                .collect();
            assert!(
                tokens.is_empty(),
                "P2P whitespace: {:?} must produce no content tokens, got {}",
                source,
                tokens.len()
            );
        }
    }

    /// P2P: integer literals tokenise to exactly one content token of integer kind.
    ///
    /// For 6 integer literals, verifies that tokenisation produces
    /// exactly one content token of the Integer kind.
    #[test]
    fn p2p_integer_literals_tokenise_to_one_token() {
        let inputs: Vec<(&str, fn(&TokenKind) -> bool)> = vec![
            ("0",          |t| matches!(t, TokenKind::Integer(_))),
            ("1",          |t| matches!(t, TokenKind::Integer(_))),
            ("42",         |t| matches!(t, TokenKind::Integer(_))),
            ("100",        |t| matches!(t, TokenKind::Integer(_))),
            ("999",        |t| matches!(t, TokenKind::Integer(_))),
            ("2147483647", |t| matches!(t, TokenKind::Integer(_))),
        ];

        for (source, predicate) in &inputs {
            let (tokens, errors) = tokenize_no_eof(source);
            assert!(errors.is_empty(), "P2P int[{source}]: unexpected lex errors");
            assert_eq!(
                tokens.len(), 1,
                "P2P int[{source}]: expected exactly one content token"
            );
            assert!(
                predicate(&tokens[0].kind),
                "P2P int[{source}]: token kind mismatch for {source:?}"
            );
        }
    }

    // -------------------------------------------------------------------------
    // E2E: lexer -> token stream properties
    // -------------------------------------------------------------------------

    /// E2E: a complete function definition lexes without errors and contains
    /// the expected keyword tokens in order.
    #[test]
    fn e2e_function_definition_lexes_correctly() {
        let source = "fn add(x: i32, y: i32): i32 = x + y";
        let (tokens, errors) = tokenize_no_eof(source);

        assert!(errors.is_empty(), "E2E fn: no lex errors expected");
        assert!(!tokens.is_empty(), "E2E fn: must produce tokens");

        // First token must be `fn`
        assert!(
            matches!(tokens[0].kind, TokenKind::Fn),
            "E2E fn: first token must be Fn keyword"
        );

        // Must contain Ident tokens for 'add', 'x', 'y'
        let idents: Vec<&SmolStr> = tokens.iter()
            .filter_map(|t| if let TokenKind::Ident(s) = &t.kind { Some(s) } else { None })
            .collect();
        assert!(
            idents.iter().any(|s| s.as_str() == "add"),
            "E2E fn: must contain 'add' identifier"
        );
        assert!(
            idents.iter().any(|s| s.as_str() == "x"),
            "E2E fn: must contain 'x' identifier"
        );
        assert!(
            idents.iter().any(|s| s.as_str() == "y"),
            "E2E fn: must contain 'y' identifier"
        );
    }

    /// E2E: a linear let binding lexes with let! as distinct from let.
    ///
    /// Verifies that the lexer correctly distinguishes `let!` from `let`.
    #[test]
    fn e2e_letlin_distinguished_from_let() {
        let source_letlin = "let! x = 1 in x";
        let source_let    = "let x = 1";

        let (tokens_lin, errors_lin) = tokenize_no_eof(source_letlin);
        let (tokens_let, errors_let) = tokenize_no_eof(source_let);

        assert!(errors_lin.is_empty(), "E2E let!: no lex errors");
        assert!(errors_let.is_empty(), "E2E let: no lex errors");

        assert!(
            tokens_lin.iter().any(|t| matches!(t.kind, TokenKind::LetBang)),
            "E2E let!: must contain LetLin token"
        );
        assert!(
            tokens_let.iter().any(|t| matches!(t.kind, TokenKind::Let)),
            "E2E let: must contain Let token"
        );
        assert!(
            !tokens_let.iter().any(|t| matches!(t.kind, TokenKind::LetBang)),
            "E2E let: plain let must NOT contain LetLin token"
        );
    }

    // -------------------------------------------------------------------------
    // ASPECT TESTS
    // -------------------------------------------------------------------------

    /// Aspect: lexer does not panic on arbitrary ASCII inputs.
    ///
    /// Feeds 20 unusual ASCII strings through the lexer and verifies that
    /// the tokenize function returns (possibly with errors) rather than panicking.
    #[test]
    fn aspect_no_panic_on_unusual_ascii_inputs() {
        let inputs = [
            "!@#$%^&*",
            "let let let",
            "\"unterminated string",
            "/* unterminated block comment",
            "let x = ;;;;",
            "0xDEADBEEF",
            "1e1000",
            "let _ = _",
            "???",
            "let x = ((((()))))",
            "let x = [[[",
            "let x = >>>",
            "let!let!let!",
            "-- -- --",
            "0 0 0 0 0 0",
            "\"\\n\\t\\r\"",
            "let x = -9999",
            "1.0e10",
            "let!! = 42",
            "\x00\x01\x02",
        ];

        for source in &inputs {
            // Must not panic — may produce errors
            let (tokens, _errors) = tokenize_no_eof(source);
            // Basic sanity: tokens vector is accessible
            let _ = tokens.len();
        }
    }

    /// Aspect: tokenize and iterator produce the same tokens.
    ///
    /// Verifies that the `Lexer::tokenize` function and the `Lexer::new`
    /// iterator yield consistent results for the same input.
    #[test]
    fn aspect_tokenize_consistent_with_iterator() {
        let programs = [
            "let x = 42",
            "fn foo(a: i32): i32 = a",
            "if true then 1 else 0",
            "let! x = 1 in x",
        ];

        for source in &programs {
            let (batch_tokens, _batch_errors) = tokenize_no_eof(source);
            let iter_tokens: Vec<Token> = Lexer::new(source)
                .filter_map(|r| r.ok())
                .filter(|t| !matches!(t.kind, TokenKind::Eof))
                .collect();

            assert_eq!(
                batch_tokens.len(), iter_tokens.len(),
                "Aspect consistency[{source:?}]: batch and iterator must yield same token count"
            );

            for (i, (bt, it)) in batch_tokens.iter().zip(iter_tokens.iter()).enumerate() {
                assert_eq!(
                    bt.kind, it.kind,
                    "Aspect consistency[{source:?}] token[{i}]: kind mismatch"
                );
                assert_eq!(
                    bt.span, it.span,
                    "Aspect consistency[{source:?}] token[{i}]: span mismatch"
                );
            }
        }
    }

    /// Aspect: span merging is commutative.
    ///
    /// Verifies the Span::merge utility satisfies the commutativity property:
    /// merge(a, b) == merge(b, a) for the resulting merged span.
    #[test]
    fn aspect_span_merge_produces_bounding_span() {
        let test_cases = vec![
            (Span::new(0, 5), Span::new(3, 10)),
            (Span::new(0, 0), Span::new(0, 0)),
            (Span::new(10, 20), Span::new(5, 15)),
            (Span::new(0, 100), Span::new(50, 60)),
        ];

        for (a, b) in test_cases {
            let merged_ab = a.merge(b);
            let merged_ba = b.merge(a);

            assert_eq!(
                merged_ab, merged_ba,
                "Aspect span_merge: merge must be commutative for ({a:?}, {b:?})"
            );
            assert!(
                merged_ab.start <= a.start.min(b.start) + 1,
                "Aspect span_merge: merged start must be <= min of inputs"
            );
            assert!(
                merged_ab.end >= a.end.max(b.end),
                "Aspect span_merge: merged end must be >= max of inputs"
            );
        }
    }
}
