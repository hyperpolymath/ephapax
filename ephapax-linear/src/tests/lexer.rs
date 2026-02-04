use crate::parser::{Lexer, Token};

#[test]
fn lexer_recognizes_keywords_and_symbols() {
    let source = r#"
        let token = Arena::new();
        fn main() {
            return token == 42;
        }
    "#;

    let tokens = Lexer::new(source).tokens;

    let expected = vec![
        Token::Let,
        Token::Ident("token".into()),
        Token::Equal,
        Token::Ident("Arena".into()),
        Token::ColonColon,
        Token::Ident("new".into()),
        Token::LParen,
        Token::RParen,
        Token::Semicolon,
        Token::Fn,
        Token::Ident("main".into()),
        Token::LParen,
        Token::RParen,
        Token::LBrace,
        Token::Return,
        Token::Ident("token".into()),
        Token::EqualEqual,
        Token::Number(42),
        Token::Semicolon,
        Token::RBrace,
        Token::Eof,
    ];

    assert_eq!(tokens, expected);
}

#[test]
fn lexer_handles_comments_and_ranges() {
    let source = r#"// line comment
let range = a .. b; /* block */"#;

    let tokens = Lexer::new(source).tokens;

    let expected = vec![
        Token::Let,
        Token::Ident("range".into()),
        Token::Equal,
        Token::Ident("a".into()),
        Token::Range,
        Token::Ident("b".into()),
        Token::Semicolon,
        Token::Eof,
    ];

    assert_eq!(tokens, expected);
}
