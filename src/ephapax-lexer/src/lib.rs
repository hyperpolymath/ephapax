// SPDX-License-Identifier: EUPL-1.2
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
            Some((Err(()), span)) => {
                Some(Err(LexerError::UnexpectedCharacter(span.start)))
            }
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
        assert_eq!(lex("+ - * / %"), vec![
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Percent,
        ]);

        assert_eq!(lex("== != < > <= >="), vec![
            TokenKind::EqEq,
            TokenKind::NotEq,
            TokenKind::Lt,
            TokenKind::Gt,
            TokenKind::LtEq,
            TokenKind::GtEq,
        ]);

        assert_eq!(lex("&& || !"), vec![
            TokenKind::AndAnd,
            TokenKind::OrOr,
            TokenKind::Not,
        ]);

        assert_eq!(lex("& @ -> = : , . ;"), vec![
            TokenKind::Ampersand,
            TokenKind::At,
            TokenKind::Arrow,
            TokenKind::Eq,
            TokenKind::Colon,
            TokenKind::Comma,
            TokenKind::Dot,
            TokenKind::Semi,
        ]);
    }

    #[test]
    fn test_delimiters() {
        assert_eq!(lex("( ) { } [ ]"), vec![
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::LBracket,
            TokenKind::RBracket,
        ]);
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
        assert_eq!(lex(r#""hello""#), vec![TokenKind::String("hello".to_string())]);
        assert_eq!(lex(r#""hello\nworld""#), vec![TokenKind::String("hello\nworld".to_string())]);
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
        assert_eq!(lex("-- this is a comment\n42"), vec![TokenKind::Integer(42)]);
        assert_eq!(lex("{- block comment -}42"), vec![TokenKind::Integer(42)]);
        assert_eq!(lex("{- nested {- comment -} -}42"), vec![TokenKind::Integer(42)]);
    }

    #[test]
    fn test_complex_expression() {
        let tokens = lex("let x = 42 in x + 1");
        assert_eq!(tokens, vec![
            TokenKind::Let,
            TokenKind::Ident("x".into()),
            TokenKind::Eq,
            TokenKind::Integer(42),
            TokenKind::In,
            TokenKind::Ident("x".into()),
            TokenKind::Plus,
            TokenKind::Integer(1),
        ]);
    }

    #[test]
    fn test_region_expression() {
        let tokens = lex(r#"region r { String.new@r("hello") }"#);
        assert_eq!(tokens, vec![
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
        ]);
    }

    #[test]
    fn test_function_definition() {
        let tokens = lex("fn add(x: I32, y: I32): I32 = x + y");
        assert_eq!(tokens, vec![
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
        ]);
    }

    #[test]
    fn test_lambda() {
        let tokens = lex("fn(x: I32) -> x + 1");
        assert_eq!(tokens, vec![
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
        ]);
    }

    #[test]
    fn test_case_expression() {
        let tokens = lex("case x of inl(n) -> n inr(b) -> 0 end");
        assert_eq!(tokens, vec![
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
        ]);
    }

    #[test]
    fn test_borrow() {
        let tokens = lex("String.len(&s)");
        assert_eq!(tokens, vec![
            TokenKind::TyString,
            TokenKind::Dot,
            TokenKind::Ident("len".into()),
            TokenKind::LParen,
            TokenKind::Ampersand,
            TokenKind::Ident("s".into()),
            TokenKind::RParen,
        ]);
    }

    #[test]
    fn test_spans() {
        let source = "let x = 42";
        let tokens: Vec<Token> = Lexer::new(source)
            .filter_map(|r| r.ok())
            .collect();

        assert_eq!(tokens[0].span, Span::new(0, 3));  // "let"
        assert_eq!(tokens[1].span, Span::new(4, 5));  // "x"
        assert_eq!(tokens[2].span, Span::new(6, 7));  // "="
        assert_eq!(tokens[3].span, Span::new(8, 10)); // "42"
    }

    #[test]
    fn test_tokenize_with_errors() {
        let (tokens, errors) = Lexer::tokenize("let x = 42 $ y");
        assert!(!errors.is_empty());
        assert!(tokens.iter().any(|t| matches!(t.kind, TokenKind::Let)));
    }
}
