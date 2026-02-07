// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Parser
//!
//! Parses Ephapax source code into an AST using the pest PEG parser.
//!
//! # Example
//!
//! ```
//! use ephapax_parser::parse;
//!
//! let source = "let x = 42 in x";
//! let result = parse(source);
//! ```

use ephapax_syntax::{BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, Span, Ty, UnaryOp};
use pest::Parser;
use pest_derive::Parser;
use smol_str::SmolStr;

pub mod error;

pub use error::{ParseError, Report};

#[derive(Parser)]
#[grammar = "ephapax.pest"]
struct EphapaxParser;

/// Parse source code into an expression
pub fn parse(source: &str) -> Result<Expr, Vec<ParseError>> {
    let pairs = EphapaxParser::parse(Rule::expression_only, source)
        .map_err(|e| vec![ParseError::Syntax {
            message: e.to_string(),
            span: Span::dummy(),
        }])?;

    let pair = pairs.into_iter().next().unwrap();
    let inner = pair.into_inner().next().unwrap();

    parse_expression(inner).map_err(|e| vec![e])
}

/// Parse source code into a module (multiple declarations)
pub fn parse_module(source: &str, name: &str) -> Result<Module, Vec<ParseError>> {
    let pairs = EphapaxParser::parse(Rule::module, source)
        .map_err(|e| vec![ParseError::Syntax {
            message: e.to_string(),
            span: Span::dummy(),
        }])?;

    let pair = pairs.into_iter().next().unwrap();
    let mut decls = Vec::new();

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::declaration {
            decls.push(parse_declaration(inner).map_err(|e| vec![e])?);
        }
    }

    Ok(Module {
        name: SmolStr::new(name),
        decls,
    })
}

// ============================================================================
// Helper Functions
// ============================================================================

fn span_from_pair(pair: &pest::iterators::Pair<Rule>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

fn parse_identifier(pair: pest::iterators::Pair<Rule>) -> SmolStr {
    SmolStr::new(pair.as_str())
}

// ============================================================================
// Declaration Parsing
// ============================================================================

fn parse_declaration(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::fn_decl => parse_fn_decl(inner),
        Rule::type_decl => parse_type_decl(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected declaration: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_fn_decl(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap());

    let mut params = Vec::new();
    let mut ret_ty = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::param_list => {
                for param in item.into_inner() {
                    if param.as_rule() == Rule::param {
                        let mut parts = param.into_inner();
                        let param_name = parse_identifier(parts.next().unwrap());
                        let param_ty = parse_type(parts.next().unwrap())?;
                        params.push((param_name, param_ty));
                    }
                }
            }
            Rule::ty => {
                if ret_ty.is_none() {
                    ret_ty = Some(parse_type(item)?);
                }
            }
            Rule::expression => {
                body = Some(parse_expression(item)?);
            }
            _ => {}
        }
    }

    Ok(Decl::Fn {
        name,
        params,
        ret_ty: ret_ty.unwrap_or(Ty::Base(BaseTy::Unit)),
        body: body.unwrap_or_else(|| Expr::dummy(ExprKind::Lit(Literal::Unit))),
    })
}

fn parse_type_decl(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let mut inner = pair.into_inner();
    let name = parse_identifier(inner.next().unwrap());
    let ty = parse_type(inner.next().unwrap())?;

    Ok(Decl::Type { name, ty })
}

// ============================================================================
// Type Parsing
// ============================================================================

fn parse_type(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    let mut inner = pair.into_inner().peekable();

    let first = inner.next().unwrap();
    let left = parse_sum_type(first)?;

    // Check for function type (->)
    if let Some(rest) = inner.next() {
        let ret = parse_type(rest)?;
        Ok(Ty::Fun {
            param: Box::new(left),
            ret: Box::new(ret),
        })
    } else {
        Ok(left)
    }
}

fn parse_sum_type(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    let mut inner = pair.into_inner();
    let mut result = parse_type_atom(inner.next().unwrap())?;

    for atom in inner {
        let right = parse_type_atom(atom)?;
        result = Ty::Sum {
            left: Box::new(result),
            right: Box::new(right),
        };
    }

    Ok(result)
}

fn parse_type_atom(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::base_ty => parse_base_type(inner),
        Rule::string_ty => {
            let region = parse_identifier(inner.into_inner().next().unwrap());
            Ok(Ty::String(region))
        }
        Rule::borrow_ty => {
            let inner_ty = parse_type_atom(inner.into_inner().next().unwrap())?;
            Ok(Ty::Borrow(Box::new(inner_ty)))
        }
        Rule::list_ty => {
            let elem_ty = parse_type(inner.into_inner().next().unwrap())?;
            Ok(Ty::List(Box::new(elem_ty)))
        }
        Rule::product_ty => {
            let mut types: Vec<Ty> = Vec::new();
            for ty_pair in inner.into_inner() {
                types.push(parse_type(ty_pair)?);
            }

            if types.len() == 1 {
                Ok(types.into_iter().next().unwrap())
            } else {
                let result = types.into_iter().reduce(|acc, t| Ty::Prod {
                    left: Box::new(acc),
                    right: Box::new(t),
                });
                Ok(result.unwrap())
            }
        }
        Rule::type_var => {
            let name = parse_identifier(inner.into_inner().next().unwrap());
            Ok(Ty::Var(name))
        }
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected type atom: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_base_type(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    let text = pair.as_str().trim();
    match text {
        "()" => Ok(Ty::Base(BaseTy::Unit)),
        "Bool" => Ok(Ty::Base(BaseTy::Bool)),
        "I32" => Ok(Ty::Base(BaseTy::I32)),
        "I64" => Ok(Ty::Base(BaseTy::I64)),
        "F32" => Ok(Ty::Base(BaseTy::F32)),
        "F64" => Ok(Ty::Base(BaseTy::F64)),
        _ => Err(ParseError::Syntax {
            message: format!("Unknown base type: {}", text),
            span: span_from_pair(&pair),
        }),
    }
}

// ============================================================================
// Expression Parsing
// ============================================================================

fn parse_expression(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::let_expr => parse_let_expr(inner),
        Rule::let_lin_expr => parse_let_lin_expr(inner),
        Rule::lambda_expr => parse_lambda_expr(inner),
        Rule::if_expr => parse_if_expr(inner),
        Rule::region_expr => parse_region_expr(inner),
        Rule::case_expr => parse_case_expr(inner),
        Rule::or_expr => parse_or_expr(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected expression: {:?}", inner.as_rule()),
            span,
        }),
    }
}

fn parse_let_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap());

    let mut ty = None;
    let mut value = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::ty => ty = Some(parse_type(item)?),
            Rule::expression => {
                if value.is_none() {
                    value = Some(parse_expression(item)?);
                } else {
                    body = Some(parse_expression(item)?);
                }
            }
            _ => {}
        }
    }

    Ok(Expr::new(
        ExprKind::Let {
            name,
            ty,
            value: Box::new(value.unwrap()),
            body: Box::new(body.unwrap()),
        },
        span,
    ))
}

fn parse_let_lin_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap());

    let mut ty = None;
    let mut value = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::ty => ty = Some(parse_type(item)?),
            Rule::expression => {
                if value.is_none() {
                    value = Some(parse_expression(item)?);
                } else {
                    body = Some(parse_expression(item)?);
                }
            }
            _ => {}
        }
    }

    Ok(Expr::new(
        ExprKind::LetLin {
            name,
            ty,
            value: Box::new(value.unwrap()),
            body: Box::new(body.unwrap()),
        },
        span,
    ))
}

fn parse_lambda_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let param = parse_identifier(inner.next().unwrap());
    let param_ty = parse_type(inner.next().unwrap())?;
    let body = parse_expression(inner.next().unwrap())?;

    Ok(Expr::new(
        ExprKind::Lambda {
            param,
            param_ty,
            body: Box::new(body),
        },
        span,
    ))
}

fn parse_if_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let cond = parse_expression(inner.next().unwrap())?;
    let then_branch = parse_expression(inner.next().unwrap())?;
    let else_branch = parse_expression(inner.next().unwrap())?;

    Ok(Expr::new(
        ExprKind::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        },
        span,
    ))
}

fn parse_region_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().unwrap());
    let body = parse_expression(inner.next().unwrap())?;

    Ok(Expr::new(
        ExprKind::Region {
            name,
            body: Box::new(body),
        },
        span,
    ))
}

fn parse_case_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let scrutinee = parse_expression(inner.next().unwrap())?;
    let left_var = parse_identifier(inner.next().unwrap());
    let left_body = parse_expression(inner.next().unwrap())?;
    let right_var = parse_identifier(inner.next().unwrap());
    let right_body = parse_expression(inner.next().unwrap())?;

    Ok(Expr::new(
        ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            left_var,
            left_body: Box::new(left_body),
            right_var,
            right_body: Box::new(right_body),
        },
        span,
    ))
}

// ============================================================================
// Binary Operator Parsing
// ============================================================================

fn parse_or_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut result = parse_and_expr(inner.next().unwrap())?;

    for and_expr in inner {
        let right = parse_and_expr(and_expr)?;
        result = Expr::new(
            ExprKind::BinOp {
                op: BinOp::Or,
                left: Box::new(result),
                right: Box::new(right),
            },
            span,
        );
    }

    Ok(result)
}

fn parse_and_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut result = parse_eq_expr(inner.next().unwrap())?;

    for eq_expr in inner {
        let right = parse_eq_expr(eq_expr)?;
        result = Expr::new(
            ExprKind::BinOp {
                op: BinOp::And,
                left: Box::new(result),
                right: Box::new(right),
            },
            span,
        );
    }

    Ok(result)
}

fn parse_eq_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner().peekable();

    let mut result = parse_cmp_expr(inner.next().unwrap())?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::eq_op {
            let op = match next.as_str() {
                "==" => BinOp::Eq,
                "!=" => BinOp::Ne,
                _ => unreachable!(),
            };
            (op, inner.next().unwrap())
        } else {
            continue;
        };

        let right = parse_cmp_expr(right_pair)?;
        result = Expr::new(
            ExprKind::BinOp {
                op,
                left: Box::new(result),
                right: Box::new(right),
            },
            span,
        );
    }

    Ok(result)
}

fn parse_cmp_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner().peekable();

    let mut result = parse_add_expr(inner.next().unwrap())?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::cmp_op {
            let op = match next.as_str() {
                "<" => BinOp::Lt,
                ">" => BinOp::Gt,
                "<=" => BinOp::Le,
                ">=" => BinOp::Ge,
                _ => unreachable!(),
            };
            (op, inner.next().unwrap())
        } else {
            continue;
        };

        let right = parse_add_expr(right_pair)?;
        result = Expr::new(
            ExprKind::BinOp {
                op,
                left: Box::new(result),
                right: Box::new(right),
            },
            span,
        );
    }

    Ok(result)
}

fn parse_add_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner().peekable();

    let mut result = parse_mul_expr(inner.next().unwrap())?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::add_op {
            let op = match next.as_str() {
                "+" => BinOp::Add,
                "-" => BinOp::Sub,
                _ => unreachable!(),
            };
            (op, inner.next().unwrap())
        } else {
            continue;
        };

        let right = parse_mul_expr(right_pair)?;
        result = Expr::new(
            ExprKind::BinOp {
                op,
                left: Box::new(result),
                right: Box::new(right),
            },
            span,
        );
    }

    Ok(result)
}

fn parse_mul_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner().peekable();

    let mut result = parse_unary_expr(inner.next().unwrap())?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::mul_op {
            let op = match next.as_str() {
                "*" => BinOp::Mul,
                "/" => BinOp::Div,
                "%" => BinOp::Mod,
                _ => unreachable!(),
            };
            (op, inner.next().unwrap())
        } else {
            continue;
        };

        let right = parse_unary_expr(right_pair)?;
        result = Expr::new(
            ExprKind::BinOp {
                op,
                left: Box::new(result),
                right: Box::new(right),
            },
            span,
        );
    }

    Ok(result)
}

fn parse_unary_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let text = pair.as_str().trim();

    if text.starts_with('!') {
        let inner = pair.into_inner().next().unwrap();
        let operand = parse_unary_expr(inner)?;
        Ok(Expr::new(
            ExprKind::UnaryOp {
                op: UnaryOp::Not,
                operand: Box::new(operand),
            },
            span,
        ))
    } else if text.starts_with('-') && !text.chars().nth(1).map_or(false, |c| c.is_ascii_digit()) {
        let inner = pair.into_inner().next().unwrap();
        let operand = parse_unary_expr(inner)?;
        Ok(Expr::new(
            ExprKind::UnaryOp {
                op: UnaryOp::Neg,
                operand: Box::new(operand),
            },
            span,
        ))
    } else {
        let inner = pair.into_inner().next().unwrap();
        parse_postfix_expr(inner)
    }
}

fn parse_postfix_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut result = parse_atom_expr(inner.next().unwrap())?;

    for op in inner {
        match op.as_rule() {
            Rule::postfix_op => {
                let op_inner = op.into_inner().next().unwrap();
                match op_inner.as_rule() {
                    Rule::call_op => {
                        let arg = parse_expression(op_inner.into_inner().next().unwrap())?;
                        result = Expr::new(
                            ExprKind::App {
                                func: Box::new(result),
                                arg: Box::new(arg),
                            },
                            span,
                        );
                    }
                    Rule::index_op => {
                        let index = parse_expression(op_inner.into_inner().next().unwrap())?;
                        result = Expr::new(
                            ExprKind::ListIndex {
                                list: Box::new(result),
                                index: Box::new(index),
                            },
                            span,
                        );
                    }
                    Rule::member_op => {
                        let member = op_inner.into_inner().next().unwrap();
                        match member.as_rule() {
                            Rule::integer => {
                                let index = member.as_str().parse::<usize>().unwrap();
                                if index == 0 {
                                    result = Expr::new(ExprKind::Fst(Box::new(result)), span);
                                } else if index == 1 {
                                    result = Expr::new(ExprKind::Snd(Box::new(result)), span);
                                } else {
                                    result = Expr::new(
                                        ExprKind::TupleIndex {
                                            tuple: Box::new(result),
                                            index,
                                        },
                                        span,
                                    );
                                }
                            }
                            Rule::identifier => {
                                // Field access by name not currently supported
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    Ok(result)
}

fn parse_atom_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::string_method => parse_string_method(inner),
        Rule::inl_expr => {
            let mut parts = inner.into_inner();
            let ty = parse_type(parts.next().unwrap())?;
            let value = parse_expression(parts.next().unwrap())?;
            Ok(Expr::new(
                ExprKind::Inl {
                    ty,
                    value: Box::new(value),
                },
                span,
            ))
        }
        Rule::inr_expr => {
            let mut parts = inner.into_inner();
            let ty = parse_type(parts.next().unwrap())?;
            let value = parse_expression(parts.next().unwrap())?;
            Ok(Expr::new(
                ExprKind::Inr {
                    ty,
                    value: Box::new(value),
                },
                span,
            ))
        }
        Rule::borrow_expr => {
            let inner_expr = parse_unary_expr(inner.into_inner().next().unwrap())?;
            Ok(Expr::new(ExprKind::Borrow(Box::new(inner_expr)), span))
        }
        Rule::drop_expr => {
            let inner_expr = parse_expression(inner.into_inner().next().unwrap())?;
            Ok(Expr::new(ExprKind::Drop(Box::new(inner_expr)), span))
        }
        Rule::copy_expr => {
            let inner_expr = parse_expression(inner.into_inner().next().unwrap())?;
            Ok(Expr::new(ExprKind::Copy(Box::new(inner_expr)), span))
        }
        Rule::list_literal => {
            let mut elements = Vec::new();
            for item in inner.into_inner() {
                if item.as_rule() == Rule::expression {
                    elements.push(parse_expression(item)?);
                }
            }
            Ok(Expr::new(ExprKind::ListLit(elements), span))
        }
        Rule::paren_or_pair => parse_paren_or_pair(inner),
        Rule::literal => parse_literal(inner),
        Rule::variable => {
            let name = parse_identifier(inner.into_inner().next().unwrap());
            Ok(Expr::new(ExprKind::Var(name), span))
        }
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected atom expression: {:?}", inner.as_rule()),
            span,
        }),
    }
}

fn parse_string_method(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let method = parse_identifier(inner.next().unwrap());

    let mut region = None;
    let mut args = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::identifier => region = Some(parse_identifier(item)),
            Rule::expr_list => {
                for expr_pair in item.into_inner() {
                    args.push(parse_expression(expr_pair)?);
                }
            }
            _ => {}
        }
    }

    match method.as_str() {
        "new" => {
            let region = region.unwrap_or_else(|| SmolStr::new("_"));
            if let Some(arg) = args.into_iter().next() {
                if let ExprKind::Lit(Literal::String(s)) = arg.kind {
                    return Ok(Expr::new(ExprKind::StringNew { region, value: s }, span));
                }
            }
            Ok(Expr::new(ExprKind::Lit(Literal::Unit), span))
        }
        "concat" => {
            let mut iter = args.into_iter();
            let left = iter.next().map(Box::new);
            let right = iter.next().map(Box::new);
            if let (Some(left), Some(right)) = (left, right) {
                Ok(Expr::new(ExprKind::StringConcat { left, right }, span))
            } else {
                Ok(Expr::new(ExprKind::Lit(Literal::Unit), span))
            }
        }
        "len" => {
            if let Some(arg) = args.into_iter().next() {
                Ok(Expr::new(ExprKind::StringLen(Box::new(arg)), span))
            } else {
                Ok(Expr::new(ExprKind::Lit(Literal::Unit), span))
            }
        }
        _ => Ok(Expr::new(ExprKind::Lit(Literal::Unit), span)),
    }
}

fn parse_paren_or_pair(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut exprs: Vec<Expr> = Vec::new();

    for item in pair.into_inner() {
        if item.as_rule() == Rule::expression {
            exprs.push(parse_expression(item)?);
        }
    }

    match exprs.len() {
        0 => Ok(Expr::new(ExprKind::Lit(Literal::Unit), span)),
        1 => Ok(exprs.into_iter().next().unwrap()),
        2 => {
            // Keep using Pair for 2-element tuples for backward compatibility
            let mut iter = exprs.into_iter();
            let left = iter.next().unwrap();
            let right = iter.next().unwrap();
            Ok(Expr::new(
                ExprKind::Pair {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            ))
        }
        _ => {
            // Use TupleLit for 3+ elements
            Ok(Expr::new(ExprKind::TupleLit(exprs), span))
        }
    }
}

fn parse_literal(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair.into_inner().next().unwrap();

    let lit = match inner.as_rule() {
        Rule::unit_literal => Literal::Unit,
        Rule::boolean => {
            if inner.as_str() == "true" {
                Literal::Bool(true)
            } else {
                Literal::Bool(false)
            }
        }
        Rule::float => {
            let n: f64 = inner.as_str().parse().unwrap_or(0.0);
            Literal::F64(n)
        }
        Rule::integer => {
            let n: i64 = inner.as_str().parse().unwrap_or(0);
            if n > i32::MAX as i64 || n < i32::MIN as i64 {
                Literal::I64(n)
            } else {
                Literal::I32(n as i32)
            }
        }
        Rule::string => {
            let s = inner.as_str();
            // Remove quotes and process escapes
            let content = &s[1..s.len()-1];
            let processed = content
                .replace("\\n", "\n")
                .replace("\\r", "\r")
                .replace("\\t", "\t")
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
            Literal::String(processed)
        }
        _ => Literal::Unit,
    };

    Ok(Expr::new(ExprKind::Lit(lit), span))
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
