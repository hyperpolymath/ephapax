// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Parser
//!
//! Parses Ephapax source code into an AST using the chumsky parser combinator library.
//!
//! # Example
//!
//! ```
//! use ephapax_parser::parse;
//!
//! let source = "let x = 42 in x";
//! let result = parse(source);
//! ```

use chumsky::prelude::*;
use ephapax_lexer::{Lexer, Span as LexerSpan, TokenKind};
use ephapax_syntax::{BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, Span as SyntaxSpan, Ty, UnaryOp};
use smol_str::SmolStr;

pub mod error;

pub use error::{ParseError, Report};

/// Convert lexer span to syntax span
fn to_syntax_span(span: LexerSpan) -> SyntaxSpan {
    SyntaxSpan::new(span.start, span.end)
}

/// Merge two syntax spans
fn merge_spans(a: SyntaxSpan, b: SyntaxSpan) -> SyntaxSpan {
    SyntaxSpan::new(a.start.min(b.start), a.end.max(b.end))
}

/// Token type that carries span information
#[derive(Debug, Clone, PartialEq)]
struct SpannedToken {
    kind: TokenKind,
    span: LexerSpan,
}

impl std::fmt::Display for SpannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

/// Parse source code into an expression
pub fn parse(source: &str) -> Result<Expr, Vec<ParseError>> {
    let (tokens, lex_errors) = Lexer::tokenize(source);

    if !lex_errors.is_empty() {
        return Err(lex_errors
            .into_iter()
            .map(|e| ParseError::Lexer(e.to_string()))
            .collect());
    }

    // Convert tokens to spanned tokens - filter out EOF for expression parsing
    let spanned_tokens: Vec<SpannedToken> = tokens
        .into_iter()
        .filter(|t| t.kind != TokenKind::Eof)
        .map(|t| SpannedToken { kind: t.kind, span: t.span })
        .collect();

    let len = source.len();
    let end_span = LexerSpan::new(len, len);

    // Parse using slice-based input
    let result = expr_parser()
        .then_ignore(end())
        .parse(&spanned_tokens[..])
        .into_result();

    result.map_err(|errs| {
        errs.into_iter()
            .map(|e| {
                // Get span from the error's location in the token stream
                let span = if let Some(&ref tok) = e.found() {
                    to_syntax_span(tok.span)
                } else {
                    to_syntax_span(end_span)
                };
                ParseError::Syntax {
                    message: format!("{}", e.reason()),
                    span,
                }
            })
            .collect()
    })
}

/// Parse source code into a module (multiple declarations)
pub fn parse_module(source: &str, name: &str) -> Result<Module, Vec<ParseError>> {
    let (tokens, lex_errors) = Lexer::tokenize(source);

    if !lex_errors.is_empty() {
        return Err(lex_errors
            .into_iter()
            .map(|e| ParseError::Lexer(e.to_string()))
            .collect());
    }

    let spanned_tokens: Vec<SpannedToken> = tokens
        .into_iter()
        .map(|t| SpannedToken { kind: t.kind, span: t.span })
        .collect();

    let len = source.len();
    let end_span = LexerSpan::new(len, len);

    let result = module_parser()
        .parse(&spanned_tokens[..])
        .into_result();

    result
        .map(|decls| Module {
            name: SmolStr::new(name),
            decls,
        })
        .map_err(|errs| {
            errs.into_iter()
                .map(|e| {
                    let span = if let Some(&ref tok) = e.found() {
                        to_syntax_span(tok.span)
                    } else {
                        to_syntax_span(end_span)
                    };
                    ParseError::Syntax {
                        message: format!("{}", e.reason()),
                        span,
                    }
                })
                .collect()
        })
}

// ============================================================================
// Helper Parsers
// ============================================================================

/// Match a specific token kind and return its span
fn token<'a>(
    kind: TokenKind,
) -> impl Parser<'a, &'a [SpannedToken], LexerSpan, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    any()
        .filter(move |t: &SpannedToken| t.kind == kind)
        .map(|t: SpannedToken| t.span)
}

/// Match a specific token kind and ignore the result
fn tok<'a>(
    kind: TokenKind,
) -> impl Parser<'a, &'a [SpannedToken], (), extra::Err<Rich<'a, SpannedToken>>> + Clone {
    token(kind).ignored()
}

/// Parse an identifier and return its name and span
fn ident<'a>() -> impl Parser<'a, &'a [SpannedToken], (SmolStr, LexerSpan), extra::Err<Rich<'a, SpannedToken>>> + Clone {
    any()
        .filter(|t: &SpannedToken| matches!(t.kind, TokenKind::Ident(_)))
        .map(|t: SpannedToken| {
            if let TokenKind::Ident(s) = t.kind {
                (s, t.span)
            } else {
                unreachable!()
            }
        })
}

/// Parse an identifier name only
fn ident_name<'a>() -> impl Parser<'a, &'a [SpannedToken], SmolStr, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    ident().map(|(name, _)| name)
}

// ============================================================================
// Type Parsers
// ============================================================================

fn base_type_parser<'a>() -> impl Parser<'a, &'a [SpannedToken], Ty, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    any()
        .filter(|t: &SpannedToken| {
            matches!(
                t.kind,
                TokenKind::Unit
                    | TokenKind::TyBool
                    | TokenKind::TyI32
                    | TokenKind::TyI64
                    | TokenKind::TyF32
                    | TokenKind::TyF64
            )
        })
        .map(|t: SpannedToken| match t.kind {
            TokenKind::Unit => Ty::Base(BaseTy::Unit),
            TokenKind::TyBool => Ty::Base(BaseTy::Bool),
            TokenKind::TyI32 => Ty::Base(BaseTy::I32),
            TokenKind::TyI64 => Ty::Base(BaseTy::I64),
            TokenKind::TyF32 => Ty::Base(BaseTy::F32),
            TokenKind::TyF64 => Ty::Base(BaseTy::F64),
            _ => unreachable!(),
        })
}

fn type_parser<'a>() -> impl Parser<'a, &'a [SpannedToken], Ty, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    recursive(|ty| {
        let base = base_type_parser();

        // String@region
        let string_ty = tok(TokenKind::TyString)
            .ignore_then(tok(TokenKind::At))
            .ignore_then(ident_name())
            .map(Ty::String);

        // &T (borrow)
        let borrow_ty = tok(TokenKind::Ampersand)
            .ignore_then(ty.clone())
            .map(|t| Ty::Borrow(Box::new(t)));

        // (T1, T2) product or parenthesized type
        let paren_ty = ty
            .clone()
            .separated_by(tok(TokenKind::Comma))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(tok(TokenKind::LParen), tok(TokenKind::RParen))
            .map(|types| {
                if types.len() == 1 {
                    types.into_iter().next().unwrap()
                } else if types.len() == 2 {
                    let mut iter = types.into_iter();
                    Ty::Prod {
                        left: Box::new(iter.next().unwrap()),
                        right: Box::new(iter.next().unwrap()),
                    }
                } else {
                    types
                        .into_iter()
                        .reduce(|acc, t| Ty::Prod {
                            left: Box::new(acc),
                            right: Box::new(t),
                        })
                        .unwrap()
                }
            });

        // Type variable
        let type_var = ident_name().map(Ty::Var);

        let atom = choice((base, string_ty, borrow_ty, paren_ty, type_var));

        // T1 + T2 (sum) - left associative
        let sum = atom.clone().foldl(
            tok(TokenKind::Plus).ignore_then(atom.clone()).repeated(),
            |left, right| Ty::Sum {
                left: Box::new(left),
                right: Box::new(right),
            },
        );

        // T1 -> T2 (function) - right associative
        sum.clone()
            .separated_by(tok(TokenKind::Arrow))
            .at_least(1)
            .collect::<Vec<_>>()
            .map(|types| {
                types
                    .into_iter()
                    .rev()
                    .reduce(|ret, param| Ty::Fun {
                        param: Box::new(param),
                        ret: Box::new(ret),
                    })
                    .unwrap()
            })
    })
}

// ============================================================================
// Expression Parsers
// ============================================================================

fn literal_parser<'a>() -> impl Parser<'a, &'a [SpannedToken], (Literal, LexerSpan), extra::Err<Rich<'a, SpannedToken>>> + Clone {
    any()
        .filter(|t: &SpannedToken| {
            matches!(
                t.kind,
                TokenKind::Unit
                    | TokenKind::True
                    | TokenKind::False
                    | TokenKind::Integer(_)
                    | TokenKind::Float(_)
                    | TokenKind::String(_)
            )
        })
        .map(|t: SpannedToken| {
            let lit = match t.kind {
                TokenKind::Unit => Literal::Unit,
                TokenKind::True => Literal::Bool(true),
                TokenKind::False => Literal::Bool(false),
                TokenKind::Integer(n) => {
                    // Check for overflow when converting i64 to i32
                    if n > i32::MAX as i64 || n < i32::MIN as i64 {
                        Literal::I64(n)
                    } else {
                        Literal::I32(n as i32)
                    }
                },
                TokenKind::Float(n) => Literal::F64(n),
                TokenKind::String(s) => Literal::String(s),
                _ => unreachable!(),
            };
            (lit, t.span)
        })
}

fn expr_parser<'a>() -> impl Parser<'a, &'a [SpannedToken], Expr, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    recursive(|expr: Recursive<dyn Parser<&[SpannedToken], Expr, extra::Err<Rich<SpannedToken>>>>| {
        // Literals
        let literal = literal_parser()
            .map(|(lit, span)| Expr::new(ExprKind::Lit(lit), to_syntax_span(span)));

        // Variables
        let var = ident()
            .map(|(name, span)| Expr::new(ExprKind::Var(name), to_syntax_span(span)));

        // String.new@r("...") or String.concat(...) etc.
        let string_method = token(TokenKind::TyString)
            .then_ignore(tok(TokenKind::Dot))
            .then(ident_name())
            .then(tok(TokenKind::At).ignore_then(ident_name()).or_not())
            .then(
                expr.clone()
                    .separated_by(tok(TokenKind::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(tok(TokenKind::LParen), tok(TokenKind::RParen)),
            )
            .map(|(((start_span, method), region), args)| {
                let span = to_syntax_span(start_span);
                match method.as_str() {
                    "new" => {
                        let region = region.unwrap_or_else(|| SmolStr::new("_"));
                        if let Some(arg) = args.into_iter().next() {
                            if let ExprKind::Lit(Literal::String(s)) = arg.kind {
                                return Expr::new(ExprKind::StringNew { region, value: s }, span);
                            }
                        }
                        Expr::new(ExprKind::Lit(Literal::Unit), span)
                    }
                    "concat" => {
                        let mut iter = args.into_iter();
                        let left = iter.next().map(Box::new);
                        let right = iter.next().map(Box::new);
                        if let (Some(left), Some(right)) = (left, right) {
                            Expr::new(ExprKind::StringConcat { left, right }, span)
                        } else {
                            Expr::new(ExprKind::Lit(Literal::Unit), span)
                        }
                    }
                    "len" => {
                        if let Some(arg) = args.into_iter().next() {
                            Expr::new(ExprKind::StringLen(Box::new(arg)), span)
                        } else {
                            Expr::new(ExprKind::Lit(Literal::Unit), span)
                        }
                    }
                    _ => Expr::new(ExprKind::Lit(Literal::Unit), span),
                }
            });

        // Parenthesized expression or pair
        let paren_expr = token(TokenKind::LParen)
            .then(
                expr.clone()
                    .separated_by(tok(TokenKind::Comma))
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .then_ignore(tok(TokenKind::RParen))
            .map(|(start_span, exprs)| {
                let span = to_syntax_span(start_span);
                if exprs.len() == 1 {
                    exprs.into_iter().next().unwrap()
                } else if exprs.len() == 2 {
                    let mut iter = exprs.into_iter();
                    Expr::new(
                        ExprKind::Pair {
                            left: Box::new(iter.next().unwrap()),
                            right: Box::new(iter.next().unwrap()),
                        },
                        span,
                    )
                } else {
                    let result = exprs.into_iter().reduce(|acc, elem| {
                        Expr::new(
                            ExprKind::Pair {
                                left: Box::new(acc),
                                right: Box::new(elem),
                            },
                            span,
                        )
                    });
                    result.unwrap()
                }
            });

        // let x = e1 in e2
        let let_expr = token(TokenKind::Let)
            .then(ident_name())
            .then(tok(TokenKind::Colon).ignore_then(type_parser()).or_not())
            .then_ignore(tok(TokenKind::Eq))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::In))
            .then(expr.clone())
            .map(|((((start_span, name), ty), value), body)| {
                Expr::new(
                    ExprKind::Let {
                        name,
                        ty,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    to_syntax_span(start_span),
                )
            });

        // let! x = e1 in e2
        let let_lin_expr = token(TokenKind::LetBang)
            .then(ident_name())
            .then(tok(TokenKind::Colon).ignore_then(type_parser()).or_not())
            .then_ignore(tok(TokenKind::Eq))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::In))
            .then(expr.clone())
            .map(|((((start_span, name), ty), value), body)| {
                Expr::new(
                    ExprKind::LetLin {
                        name,
                        ty,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    to_syntax_span(start_span),
                )
            });

        // fn(x: T) -> e
        let lambda = token(TokenKind::Fn)
            .then_ignore(tok(TokenKind::LParen))
            .then(ident_name())
            .then_ignore(tok(TokenKind::Colon))
            .then(type_parser())
            .then_ignore(tok(TokenKind::RParen))
            .then_ignore(tok(TokenKind::Arrow))
            .then(expr.clone())
            .map(|(((start_span, param), param_ty), body)| {
                Expr::new(
                    ExprKind::Lambda {
                        param,
                        param_ty,
                        body: Box::new(body),
                    },
                    to_syntax_span(start_span),
                )
            });

        // if e1 then e2 else e3
        let if_expr = token(TokenKind::If)
            .then(expr.clone())
            .then_ignore(tok(TokenKind::Then))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::Else))
            .then(expr.clone())
            .map(|(((start_span, cond), then_branch), else_branch)| {
                Expr::new(
                    ExprKind::If {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    to_syntax_span(start_span),
                )
            });

        // region r { e }
        let region_expr = token(TokenKind::Region)
            .then(ident_name())
            .then_ignore(tok(TokenKind::LBrace))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::RBrace))
            .map(|((start_span, name), body)| {
                Expr::new(
                    ExprKind::Region {
                        name,
                        body: Box::new(body),
                    },
                    to_syntax_span(start_span),
                )
            });

        // inl[T](e)
        let inl_expr = token(TokenKind::Inl)
            .then_ignore(tok(TokenKind::LBracket))
            .then(type_parser())
            .then_ignore(tok(TokenKind::RBracket))
            .then_ignore(tok(TokenKind::LParen))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::RParen))
            .map(|((start_span, ty), value)| {
                Expr::new(
                    ExprKind::Inl {
                        ty,
                        value: Box::new(value),
                    },
                    to_syntax_span(start_span),
                )
            });

        // inr[T](e)
        let inr_expr = token(TokenKind::Inr)
            .then_ignore(tok(TokenKind::LBracket))
            .then(type_parser())
            .then_ignore(tok(TokenKind::RBracket))
            .then_ignore(tok(TokenKind::LParen))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::RParen))
            .map(|((start_span, ty), value)| {
                Expr::new(
                    ExprKind::Inr {
                        ty,
                        value: Box::new(value),
                    },
                    to_syntax_span(start_span),
                )
            });

        // case e of inl(x) -> e1 inr(y) -> e2 end
        let case_expr = token(TokenKind::Case)
            .then(expr.clone())
            .then_ignore(tok(TokenKind::Of))
            .then_ignore(tok(TokenKind::Inl))
            .then_ignore(tok(TokenKind::LParen))
            .then(ident_name())
            .then_ignore(tok(TokenKind::RParen))
            .then_ignore(tok(TokenKind::Arrow))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::Inr))
            .then_ignore(tok(TokenKind::LParen))
            .then(ident_name())
            .then_ignore(tok(TokenKind::RParen))
            .then_ignore(tok(TokenKind::Arrow))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::End))
            .map(
                |(((((start_span, scrutinee), left_var), left_body), right_var), right_body)| {
                    Expr::new(
                        ExprKind::Case {
                            scrutinee: Box::new(scrutinee),
                            left_var,
                            left_body: Box::new(left_body),
                            right_var,
                            right_body: Box::new(right_body),
                        },
                        to_syntax_span(start_span),
                    )
                },
            );

        // &e (borrow)
        let borrow_expr = token(TokenKind::Ampersand)
            .then(expr.clone())
            .map(|(start_span, inner)| {
                Expr::new(ExprKind::Borrow(Box::new(inner)), to_syntax_span(start_span))
            });

        // drop(e)
        let drop_expr = token(TokenKind::Drop)
            .then_ignore(tok(TokenKind::LParen))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::RParen))
            .map(|(start_span, inner)| {
                Expr::new(ExprKind::Drop(Box::new(inner)), to_syntax_span(start_span))
            });

        // copy(e)
        let copy_expr = token(TokenKind::Copy)
            .then_ignore(tok(TokenKind::LParen))
            .then(expr.clone())
            .then_ignore(tok(TokenKind::RParen))
            .map(|(start_span, inner)| {
                Expr::new(ExprKind::Copy(Box::new(inner)), to_syntax_span(start_span))
            });

        // Atom expressions
        let atom = choice((
            string_method,
            let_expr,
            let_lin_expr,
            lambda,
            if_expr,
            region_expr,
            inl_expr,
            inr_expr,
            case_expr,
            borrow_expr,
            drop_expr,
            copy_expr,
            literal,
            paren_expr,
            var,
        ));

        // Function application and member access
        let call_or_member = atom.clone().foldl(
            choice((
                // Function application: f(arg)
                expr.clone()
                    .delimited_by(tok(TokenKind::LParen), tok(TokenKind::RParen))
                    .map(|arg| ("call".to_string(), Some(arg))),
                // Member access: e.0 or e.1 or e.field
                tok(TokenKind::Dot)
                    .ignore_then(
                        any()
                            .filter(|t: &SpannedToken| {
                                matches!(t.kind, TokenKind::Integer(_) | TokenKind::Ident(_))
                            })
                            .map(|t: SpannedToken| match t.kind {
                                TokenKind::Integer(0) => "0".to_string(),
                                TokenKind::Integer(1) => "1".to_string(),
                                TokenKind::Ident(s) => s.to_string(),
                                _ => "".to_string(),
                            }),
                    )
                    .map(|member| (member, None)),
            ))
            .repeated(),
            |func, (op, arg): (String, Option<Expr>)| {
                let span = func.span;
                match op.as_str() {
                    "call" => {
                        if let Some(arg) = arg {
                            Expr::new(
                                ExprKind::App {
                                    func: Box::new(func),
                                    arg: Box::new(arg),
                                },
                                span,
                            )
                        } else {
                            func
                        }
                    }
                    "0" => Expr::new(ExprKind::Fst(Box::new(func)), span),
                    "1" => Expr::new(ExprKind::Snd(Box::new(func)), span),
                    _ => func,
                }
            },
        );

        // Unary operators: ! and -
        let unary = choice((
            tok(TokenKind::Not)
                .ignore_then(call_or_member.clone())
                .map(|operand| {
                    let span = operand.span;
                    Expr::new(
                        ExprKind::UnaryOp {
                            op: UnaryOp::Not,
                            operand: Box::new(operand),
                        },
                        span,
                    )
                }),
            tok(TokenKind::Minus)
                .ignore_then(call_or_member.clone())
                .map(|operand| {
                    let span = operand.span;
                    Expr::new(
                        ExprKind::UnaryOp {
                            op: UnaryOp::Neg,
                            operand: Box::new(operand),
                        },
                        span,
                    )
                }),
            call_or_member,
        ));

        // Multiplicative: * / %
        let product = unary.clone().foldl(
            choice((
                token(TokenKind::Star).map(|_| BinOp::Mul),
                token(TokenKind::Slash).map(|_| BinOp::Div),
                token(TokenKind::Percent).map(|_| BinOp::Mod),
            ))
            .then(unary.clone())
            .repeated(),
            |left, (op, right)| {
                let span = merge_spans(left.span, right.span);
                Expr::new(
                    ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span,
                )
            },
        );

        // Additive: + -
        let sum = product.clone().foldl(
            choice((
                token(TokenKind::Plus).map(|_| BinOp::Add),
                token(TokenKind::Minus).map(|_| BinOp::Sub),
            ))
            .then(product.clone())
            .repeated(),
            |left, (op, right)| {
                let span = merge_spans(left.span, right.span);
                Expr::new(
                    ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span,
                )
            },
        );

        // Comparison: < > <= >=
        let comparison = sum.clone().foldl(
            choice((
                token(TokenKind::Lt).map(|_| BinOp::Lt),
                token(TokenKind::Gt).map(|_| BinOp::Gt),
                token(TokenKind::LtEq).map(|_| BinOp::Le),
                token(TokenKind::GtEq).map(|_| BinOp::Ge),
            ))
            .then(sum.clone())
            .repeated(),
            |left, (op, right)| {
                let span = merge_spans(left.span, right.span);
                Expr::new(
                    ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span,
                )
            },
        );

        // Equality: == !=
        let equality = comparison.clone().foldl(
            choice((
                token(TokenKind::EqEq).map(|_| BinOp::Eq),
                token(TokenKind::NotEq).map(|_| BinOp::Ne),
            ))
            .then(comparison.clone())
            .repeated(),
            |left, (op, right)| {
                let span = merge_spans(left.span, right.span);
                Expr::new(
                    ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span,
                )
            },
        );

        // Logical AND: &&
        let and = equality.clone().foldl(
            token(TokenKind::AndAnd)
                .map(|_| BinOp::And)
                .then(equality.clone())
                .repeated(),
            |left, (op, right)| {
                let span = merge_spans(left.span, right.span);
                Expr::new(
                    ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span,
                )
            },
        );

        // Logical OR: ||
        and.clone().foldl(
            token(TokenKind::OrOr)
                .map(|_| BinOp::Or)
                .then(and.clone())
                .repeated(),
            |left, (op, right)| {
                let span = merge_spans(left.span, right.span);
                Expr::new(
                    ExprKind::BinOp {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span,
                )
            },
        )
    })
}

// ============================================================================
// Declaration Parsers
// ============================================================================

fn decl_parser<'a>() -> impl Parser<'a, &'a [SpannedToken], Decl, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    // fn name(params): RetTy = body
    let fn_decl = tok(TokenKind::Fn)
        .ignore_then(ident_name())
        .then(
            ident_name()
                .then_ignore(tok(TokenKind::Colon))
                .then(type_parser())
                .separated_by(tok(TokenKind::Comma))
                .collect::<Vec<_>>()
                .delimited_by(tok(TokenKind::LParen), tok(TokenKind::RParen)),
        )
        .then_ignore(tok(TokenKind::Colon))
        .then(type_parser())
        .then_ignore(tok(TokenKind::Eq))
        .then(expr_parser())
        .map(|(((name, params), ret_ty), body)| Decl::Fn {
            name,
            params,
            ret_ty,
            body,
        });

    // type Name = Type
    let type_decl = tok(TokenKind::Type)
        .ignore_then(ident_name())
        .then_ignore(tok(TokenKind::Eq))
        .then(type_parser())
        .map(|(name, ty)| Decl::Type { name, ty });

    choice((fn_decl, type_decl))
}

fn module_parser<'a>() -> impl Parser<'a, &'a [SpannedToken], Vec<Decl>, extra::Err<Rich<'a, SpannedToken>>> + Clone {
    decl_parser()
        .repeated()
        .collect()
        .then_ignore(tok(TokenKind::Eof))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_ok(source: &str) -> Expr {
        parse(source).expect("parse should succeed")
    }

    #[test]
    fn test_parse_literal() {
        let expr = parse_ok("42");
        assert!(matches!(expr.kind, ExprKind::Lit(Literal::I32(42))));
    }

    #[test]
    fn test_parse_bool() {
        let expr = parse_ok("true");
        assert!(matches!(expr.kind, ExprKind::Lit(Literal::Bool(true))));
    }

    #[test]
    fn test_parse_unit() {
        let expr = parse_ok("()");
        assert!(matches!(expr.kind, ExprKind::Lit(Literal::Unit)));
    }

    #[test]
    fn test_parse_variable() {
        let expr = parse_ok("x");
        if let ExprKind::Var(name) = expr.kind {
            assert_eq!(name, "x");
        } else {
            panic!("Expected variable");
        }
    }

    #[test]
    fn test_parse_let() {
        let expr = parse_ok("let x = 42 in x");
        if let ExprKind::Let {
            name, value, body, ..
        } = expr.kind
        {
            assert_eq!(name, "x");
            assert!(matches!(value.kind, ExprKind::Lit(Literal::I32(42))));
            assert!(matches!(body.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected let expression");
        }
    }

    #[test]
    fn test_parse_lambda() {
        let expr = parse_ok("fn(x: I32) -> x");
        if let ExprKind::Lambda {
            param,
            param_ty,
            body,
        } = expr.kind
        {
            assert_eq!(param, "x");
            assert_eq!(param_ty, Ty::Base(BaseTy::I32));
            assert!(matches!(body.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected lambda");
        }
    }

    #[test]
    fn test_parse_if() {
        let expr = parse_ok("if true then 1 else 0");
        if let ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } = expr.kind
        {
            assert!(matches!(cond.kind, ExprKind::Lit(Literal::Bool(true))));
            assert!(matches!(then_branch.kind, ExprKind::Lit(Literal::I32(1))));
            assert!(matches!(else_branch.kind, ExprKind::Lit(Literal::I32(0))));
        } else {
            panic!("Expected if expression");
        }
    }

    #[test]
    fn test_parse_region() {
        let expr = parse_ok("region r { 42 }");
        if let ExprKind::Region { name, body } = expr.kind {
            assert_eq!(name, "r");
            assert!(matches!(body.kind, ExprKind::Lit(Literal::I32(42))));
        } else {
            panic!("Expected region expression");
        }
    }

    #[test]
    fn test_parse_pair() {
        let expr = parse_ok("(1, 2)");
        if let ExprKind::Pair { left, right } = expr.kind {
            assert!(matches!(left.kind, ExprKind::Lit(Literal::I32(1))));
            assert!(matches!(right.kind, ExprKind::Lit(Literal::I32(2))));
        } else {
            panic!("Expected pair");
        }
    }

    #[test]
    fn test_parse_borrow() {
        let expr = parse_ok("&x");
        if let ExprKind::Borrow(inner) = expr.kind {
            assert!(matches!(inner.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected borrow");
        }
    }

    #[test]
    fn test_parse_drop() {
        let expr = parse_ok("drop(x)");
        if let ExprKind::Drop(inner) = expr.kind {
            assert!(matches!(inner.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected drop");
        }
    }

    #[test]
    fn test_parse_copy() {
        let expr = parse_ok("copy(x)");
        if let ExprKind::Copy(inner) = expr.kind {
            assert!(matches!(inner.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected copy");
        }
    }

    #[test]
    fn test_parse_inl() {
        let expr = parse_ok("inl[Bool](42)");
        if let ExprKind::Inl { ty, value } = expr.kind {
            assert_eq!(ty, Ty::Base(BaseTy::Bool));
            assert!(matches!(value.kind, ExprKind::Lit(Literal::I32(42))));
        } else {
            panic!("Expected inl");
        }
    }

    #[test]
    fn test_parse_inr() {
        let expr = parse_ok("inr[I32](true)");
        if let ExprKind::Inr { ty, value } = expr.kind {
            assert_eq!(ty, Ty::Base(BaseTy::I32));
            assert!(matches!(value.kind, ExprKind::Lit(Literal::Bool(true))));
        } else {
            panic!("Expected inr");
        }
    }

    #[test]
    fn test_parse_case() {
        let expr = parse_ok("case x of inl(n) -> n inr(b) -> 0 end");
        if let ExprKind::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } = expr.kind
        {
            assert!(matches!(scrutinee.kind, ExprKind::Var(_)));
            assert_eq!(left_var, "n");
            assert_eq!(right_var, "b");
            assert!(matches!(left_body.kind, ExprKind::Var(_)));
            assert!(matches!(right_body.kind, ExprKind::Lit(Literal::I32(0))));
        } else {
            panic!("Expected case expression");
        }
    }

    #[test]
    fn test_parse_application() {
        let expr = parse_ok("f(x)");
        if let ExprKind::App { func, arg } = expr.kind {
            assert!(matches!(func.kind, ExprKind::Var(_)));
            assert!(matches!(arg.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected application");
        }
    }

    #[test]
    fn test_parse_projection() {
        let expr = parse_ok("p.0");
        if let ExprKind::Fst(inner) = expr.kind {
            assert!(matches!(inner.kind, ExprKind::Var(_)));
        } else {
            panic!("Expected fst projection");
        }
    }

    #[test]
    fn test_parse_module() {
        let source = r#"
            fn add(x: I32, y: I32): I32 = x
            fn id(x: I32): I32 = x
        "#;
        let module = parse_module(source, "test").expect("should parse");
        assert_eq!(module.decls.len(), 2);
    }
}
