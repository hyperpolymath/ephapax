// SPDX-License-Identifier: PMPL-1.0-or-later
// Parser support for lists and tuples

use crate::{ParseError, Parser, Result};
use ephapax_lexer::TokenKind;
use ephapax_syntax::{Expr, ExprKind, Pattern, Span};

impl<'a> Parser<'a> {
    /// Parse list literal: [e1, e2, e3]
    pub(crate) fn parse_list_literal(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        // Expect '['
        self.expect(TokenKind::LBracket)?;

        let mut elements = Vec::new();

        // Empty list []
        if self.check(TokenKind::RBracket) {
            let end = self.current_span().end;
            self.advance();
            return Ok(Expr::new(ExprKind::ListLit(elements), Span::new(start, end)));
        }

        // Parse first element
        elements.push(self.parse_expr()?);

        // Parse remaining elements
        while self.check(TokenKind::Comma) {
            self.advance(); // consume comma

            // Allow trailing comma: [1, 2, 3,]
            if self.check(TokenKind::RBracket) {
                break;
            }

            elements.push(self.parse_expr()?);
        }

        // Expect ']'
        let end = self.expect(TokenKind::RBracket)?.end;

        Ok(Expr::new(ExprKind::ListLit(elements), Span::new(start, end)))
    }

    /// Parse tuple literal or parenthesized expression: (e1, e2, e3)
    pub(crate) fn parse_tuple_or_paren(&mut self) -> Result<Expr> {
        let start = self.current_span().start;

        // Expect '('
        self.expect(TokenKind::LParen)?;

        // Unit: ()
        if self.check(TokenKind::RParen) {
            let end = self.current_span().end;
            self.advance();
            return Ok(Expr::new(
                ExprKind::Lit(ephapax_syntax::Literal::Unit),
                Span::new(start, end),
            ));
        }

        // Parse first expression
        let first = self.parse_expr()?;

        // Check if it's a tuple or just parentheses
        if self.check(TokenKind::Comma) {
            // It's a tuple
            let mut elements = vec![first];

            while self.check(TokenKind::Comma) {
                self.advance(); // consume comma

                // Allow trailing comma: (1, 2, 3,)
                if self.check(TokenKind::RParen) {
                    break;
                }

                elements.push(self.parse_expr()?);
            }

            let end = self.expect(TokenKind::RParen)?.end;

            // Single-element tuple is just the element
            if elements.len() == 1 {
                Ok(elements.into_iter().next().unwrap())
            } else {
                Ok(Expr::new(ExprKind::TupleLit(elements), Span::new(start, end)))
            }
        } else {
            // Just parentheses
            self.expect(TokenKind::RParen)?;
            Ok(first)
        }
    }

    /// Parse list index: expr[index]
    pub(crate) fn parse_list_index(&mut self, list: Expr) -> Result<Expr> {
        let start = list.span.start;

        // Expect '['
        self.expect(TokenKind::LBracket)?;

        // Parse index expression
        let index = Box::new(self.parse_expr()?);

        // Expect ']'
        let end = self.expect(TokenKind::RBracket)?.end;

        Ok(Expr::new(
            ExprKind::ListIndex {
                list: Box::new(list),
                index,
            },
            Span::new(start, end),
        ))
    }

    /// Parse tuple field access: expr.N
    pub(crate) fn parse_tuple_index(&mut self, tuple: Expr) -> Result<Expr> {
        let start = tuple.span.start;

        // Expect '.'
        self.expect(TokenKind::Dot)?;

        // Expect number
        let tok = self.current();
        if let TokenKind::IntLit(n) = tok.kind {
            let index = n as usize;
            let end = tok.span.end;
            self.advance();

            Ok(Expr::new(
                ExprKind::TupleIndex {
                    tuple: Box::new(tuple),
                    index,
                },
                Span::new(start, end),
            ))
        } else {
            Err(ParseError::Expected {
                expected: "integer for tuple field access".to_string(),
                found: format!("{:?}", tok.kind),
                span: tok.span,
            })
        }
    }

    /// Parse tuple pattern: (p1, p2, p3)
    pub(crate) fn parse_tuple_pattern(&mut self) -> Result<Pattern> {
        // Expect '('
        self.expect(TokenKind::LParen)?;

        // Unit pattern ()
        if self.check(TokenKind::RParen) {
            self.advance();
            return Ok(Pattern::Unit);
        }

        // Parse first pattern
        let first = self.parse_pattern()?;

        // Check if it's a tuple pattern
        if self.check(TokenKind::Comma) {
            let mut patterns = vec![first];

            while self.check(TokenKind::Comma) {
                self.advance(); // consume comma

                // Allow trailing comma
                if self.check(TokenKind::RParen) {
                    break;
                }

                patterns.push(self.parse_pattern()?);
            }

            self.expect(TokenKind::RParen)?;

            // Use existing Pair for 2-element tuples, Tuple for others
            if patterns.len() == 2 {
                Ok(Pattern::Pair(
                    Box::new(patterns[0].clone()),
                    Box::new(patterns[1].clone()),
                ))
            } else {
                Ok(Pattern::Tuple(patterns))
            }
        } else {
            // Just parenthesized pattern
            self.expect(TokenKind::RParen)?;
            Ok(first)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_lexer::Lexer;

    fn parse_expr_helper(source: &str) -> Result<Expr> {
        let tokens: Vec<_> = Lexer::new(source).collect();
        let mut parser = Parser::new(&tokens);
        parser.parse_expr()
    }

    #[test]
    fn test_parse_empty_list() {
        let expr = parse_expr_helper("[]").unwrap();
        match expr.kind {
            ExprKind::ListLit(elements) => assert_eq!(elements.len(), 0),
            _ => panic!("Expected ListLit"),
        }
    }

    #[test]
    fn test_parse_list_literal() {
        let expr = parse_expr_helper("[1, 2, 3]").unwrap();
        match expr.kind {
            ExprKind::ListLit(elements) => assert_eq!(elements.len(), 3),
            _ => panic!("Expected ListLit"),
        }
    }

    #[test]
    fn test_parse_tuple_literal() {
        let expr = parse_expr_helper("(1, 2, 3)").unwrap();
        match expr.kind {
            ExprKind::TupleLit(elements) => assert_eq!(elements.len(), 3),
            _ => panic!("Expected TupleLit"),
        }
    }

    #[test]
    fn test_parse_unit() {
        let expr = parse_expr_helper("()").unwrap();
        match expr.kind {
            ExprKind::Lit(ephapax_syntax::Literal::Unit) => {}
            _ => panic!("Expected Unit literal"),
        }
    }

    #[test]
    fn test_parse_list_index() {
        let expr = parse_expr_helper("list[0]").unwrap();
        match expr.kind {
            ExprKind::ListIndex { .. } => {}
            _ => panic!("Expected ListIndex"),
        }
    }

    #[test]
    fn test_parse_tuple_index() {
        let expr = parse_expr_helper("tuple.0").unwrap();
        match expr.kind {
            ExprKind::TupleIndex { index, .. } => assert_eq!(index, 0),
            _ => panic!("Expected TupleIndex"),
        }
    }
}
