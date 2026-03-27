// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! Surface AST Parser
//!
//! Parses ephapax source code into the [`SurfaceModule`] AST, which includes
//! `data` declarations, `match` expressions, and named constructors.
//!
//! Strategy: reuse the existing core parser for all shared expression forms,
//! then lift the result to surface AST. Only `data`, `match`, and `Construct`
//! are parsed directly to surface AST.

use ephapax_surface::{
    BaseTy, BinOp, ConstructorDef, DataDecl, Literal, MatchArm, Pattern, Span, SurfaceDecl,
    SurfaceExpr, SurfaceExprKind, SurfaceModule, SurfaceTy, UnaryOp,
};
use pest::Parser;
use smol_str::SmolStr;

use crate::error::ParseError;
use crate::{EphapaxParser, Rule};

// =========================================================================
// Public entry points
// =========================================================================

/// Parse source code into a surface module.
///
/// This is the primary entry point for the new two-layer pipeline:
/// `parse_surface_module` → `desugar` → core module → type check → codegen.
pub fn parse_surface_module(source: &str, name: &str) -> Result<SurfaceModule, Vec<ParseError>> {
    let pairs = EphapaxParser::parse(Rule::module, source).map_err(|e| {
        vec![ParseError::Syntax {
            message: e.to_string(),
            span: Span::dummy(),
        }]
    })?;

    let pair = pairs
        .into_iter()
        .next()
        .ok_or_else(|| vec![ParseError::unexpected_end("module")])?;

    let mut decls = Vec::new();

    for inner in pair.into_inner() {
        if inner.as_rule() == Rule::declaration {
            decls.push(parse_surface_declaration(inner).map_err(|e| vec![e])?);
        }
    }

    Ok(SurfaceModule {
        name: SmolStr::new(name),
        decls,
    })
}

/// Parse a single expression into surface AST.
pub fn parse_surface_expr(source: &str) -> Result<SurfaceExpr, Vec<ParseError>> {
    let pairs = EphapaxParser::parse(Rule::expression_only, source).map_err(|e| {
        vec![ParseError::Syntax {
            message: e.to_string(),
            span: Span::dummy(),
        }]
    })?;

    let pair = pairs
        .into_iter()
        .next()
        .ok_or_else(|| vec![ParseError::unexpected_end("expression")])?;
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| vec![ParseError::unexpected_end("inner expression")])?;

    parse_expression(inner).map_err(|e| vec![e])
}

// =========================================================================
// Helpers
// =========================================================================

fn span_from_pair(pair: &pest::iterators::Pair<Rule>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

fn parse_identifier(pair: pest::iterators::Pair<Rule>) -> SmolStr {
    SmolStr::new(pair.as_str())
}

fn parse_constructor_name(pair: pest::iterators::Pair<Rule>) -> SmolStr {
    SmolStr::new(pair.as_str())
}

// =========================================================================
// Declaration parsing
// =========================================================================

fn parse_surface_declaration(
    pair: pest::iterators::Pair<Rule>,
) -> Result<SurfaceDecl, ParseError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("declaration"))?;

    match inner.as_rule() {
        Rule::data_decl => parse_data_decl(inner),
        Rule::fn_decl => parse_fn_decl(inner),
        Rule::type_decl => parse_type_decl(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected declaration: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_data_decl(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_constructor_name(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("data type name"))?,
    );

    let mut params = Vec::new();
    let mut constructors = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::type_params => {
                for p in item.into_inner() {
                    if p.as_rule() == Rule::identifier {
                        params.push(parse_identifier(p));
                    }
                }
            }
            Rule::data_variant => {
                constructors.push(parse_data_variant(item)?);
            }
            _ => {}
        }
    }

    Ok(SurfaceDecl::Data(DataDecl {
        name,
        params,
        constructors,
        span,
    }))
}

fn parse_data_variant(pair: pest::iterators::Pair<Rule>) -> Result<ConstructorDef, ParseError> {
    let mut inner = pair.into_inner();

    let name = parse_constructor_name(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("constructor name"))?,
    );

    let mut fields = Vec::new();
    for item in inner {
        match item.as_rule() {
            Rule::ty_list => {
                for ty_pair in item.into_inner() {
                    if ty_pair.as_rule() == Rule::ty {
                        fields.push(parse_type(ty_pair)?);
                    }
                }
            }
            Rule::ty => {
                fields.push(parse_type(item)?);
            }
            _ => {}
        }
    }

    Ok(ConstructorDef { name, fields })
}

fn parse_fn_decl(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    let mut inner = pair.into_inner();

    let name = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("function name"))?,
    );

    let mut params = Vec::new();
    let mut ret_ty = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::param_list => {
                for param in item.into_inner() {
                    if param.as_rule() == Rule::param {
                        let mut parts = param.into_inner();
                        let param_name = parse_identifier(
                            parts
                                .next()
                                .ok_or_else(|| ParseError::missing("parameter name"))?,
                        );
                        let param_ty = parse_type(
                            parts
                                .next()
                                .ok_or_else(|| ParseError::missing("parameter type"))?,
                        )?;
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

    Ok(SurfaceDecl::Fn {
        name,
        params,
        ret_ty: ret_ty.unwrap_or(SurfaceTy::Base(BaseTy::Unit)),
        body: body.unwrap_or_else(|| SurfaceExpr::dummy(SurfaceExprKind::Lit(Literal::Unit))),
    })
}

fn parse_type_decl(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    let mut inner = pair.into_inner();
    let name = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("type name"))?,
    );

    let next = inner
        .next()
        .ok_or_else(|| ParseError::missing("type definition"))?;

    let ty = parse_type(next)?;

    Ok(SurfaceDecl::Type { name, ty })
}

// =========================================================================
// Expression parsing
// =========================================================================

fn parse_expression(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("expression"))?;

    match inner.as_rule() {
        Rule::let_expr => parse_let_expr(inner),
        Rule::let_lin_expr => parse_let_lin_expr(inner),
        Rule::lambda_expr => parse_lambda_expr(inner),
        Rule::if_expr => parse_if_expr(inner),
        Rule::region_expr => parse_region_expr(inner),
        Rule::match_expr => parse_match_expr(inner),
        Rule::case_expr => parse_case_expr(inner),
        Rule::or_expr => parse_or_expr(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected expression rule: {:?}", inner.as_rule()),
            span,
        }),
    }
}

fn parse_let_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("let name"))?);

    let mut ty = None;
    let mut value = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::ty if ty.is_none() => ty = Some(parse_type(item)?),
            Rule::expression if value.is_none() => value = Some(parse_expression(item)?),
            Rule::expression => body = Some(parse_expression(item)?),
            _ => {}
        }
    }

    Ok(SurfaceExpr::new(
        SurfaceExprKind::Let {
            name,
            ty,
            value: Box::new(
                value.ok_or_else(|| ParseError::missing("let value"))?,
            ),
            body: Box::new(
                body.ok_or_else(|| ParseError::missing("let body"))?,
            ),
        },
        span,
    ))
}

fn parse_let_lin_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("let! name"))?);

    let mut ty = None;
    let mut value = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::ty if ty.is_none() => ty = Some(parse_type(item)?),
            Rule::expression if value.is_none() => value = Some(parse_expression(item)?),
            Rule::expression => body = Some(parse_expression(item)?),
            _ => {}
        }
    }

    Ok(SurfaceExpr::new(
        SurfaceExprKind::LetLin {
            name,
            ty,
            value: Box::new(
                value.ok_or_else(|| ParseError::missing("let! value"))?,
            ),
            body: Box::new(
                body.ok_or_else(|| ParseError::missing("let! body"))?,
            ),
        },
        span,
    ))
}

fn parse_lambda_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let param = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("param"))?);
    let param_ty = parse_type(inner.next().ok_or_else(|| ParseError::missing("param type"))?)?;
    let body = parse_expression(inner.next().ok_or_else(|| ParseError::missing("lambda body"))?)?;

    Ok(SurfaceExpr::new(
        SurfaceExprKind::Lambda {
            param,
            param_ty,
            body: Box::new(body),
        },
        span,
    ))
}

fn parse_if_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let cond = parse_expression(inner.next().ok_or_else(|| ParseError::missing("if cond"))?)?;
    let then_b = parse_expression(inner.next().ok_or_else(|| ParseError::missing("then"))?)?;
    let else_b = parse_expression(inner.next().ok_or_else(|| ParseError::missing("else"))?)?;

    Ok(SurfaceExpr::new(
        SurfaceExprKind::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        },
        span,
    ))
}

fn parse_region_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("region name"))?);
    let body = parse_expression(inner.next().ok_or_else(|| ParseError::missing("region body"))?)?;

    Ok(SurfaceExpr::new(
        SurfaceExprKind::Region {
            name,
            body: Box::new(body),
        },
        span,
    ))
}

fn parse_case_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let scrutinee = parse_expression(inner.next().ok_or_else(|| ParseError::missing("case scrutinee"))?)?;
    let left_var = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("inl var"))?);
    let left_body = parse_expression(inner.next().ok_or_else(|| ParseError::missing("inl body"))?)?;
    let right_var = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("inr var"))?);
    let right_body = parse_expression(inner.next().ok_or_else(|| ParseError::missing("inr body"))?)?;

    Ok(SurfaceExpr::new(
        SurfaceExprKind::Case {
            scrutinee: Box::new(scrutinee),
            left_var,
            left_body: Box::new(left_body),
            right_var,
            right_body: Box::new(right_body),
        },
        span,
    ))
}

// =========================================================================
// Match expression parsing (surface-only)
// =========================================================================

fn parse_match_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let scrutinee = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("match scrutinee"))?,
    )?;

    let mut arms = Vec::new();
    for item in inner {
        if item.as_rule() == Rule::match_arm {
            arms.push(parse_match_arm(item)?);
        }
    }

    Ok(SurfaceExpr::new(
        SurfaceExprKind::Match {
            scrutinee: Box::new(scrutinee),
            arms,
        },
        span,
    ))
}

fn parse_match_arm(pair: pest::iterators::Pair<Rule>) -> Result<MatchArm, ParseError> {
    let mut inner = pair.into_inner();

    let pattern = parse_pattern(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("match pattern"))?,
    )?;

    // Remaining items: optional guard (expression before =>), then body (expression after =>)
    let mut exprs: Vec<pest::iterators::Pair<Rule>> = inner
        .filter(|p| p.as_rule() == Rule::expression)
        .collect();

    let (guard, body) = if exprs.len() >= 2 {
        let body = parse_expression(exprs.pop().unwrap())?;
        let guard_expr = parse_expression(exprs.pop().unwrap())?;
        (Some(Box::new(guard_expr)), body)
    } else if exprs.len() == 1 {
        (None, parse_expression(exprs.pop().unwrap())?)
    } else {
        return Err(ParseError::missing("match arm body"));
    };

    Ok(MatchArm {
        pattern,
        guard,
        body,
    })
}

fn parse_pattern(pair: pest::iterators::Pair<Rule>) -> Result<Pattern, ParseError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("pattern"))?;

    match inner.as_rule() {
        Rule::constructor_pattern => parse_constructor_pattern(inner),
        Rule::pair_pattern => {
            let mut parts = inner.into_inner();
            let left = parse_pattern(parts.next().ok_or_else(|| ParseError::missing("left pattern"))?)?;
            let right = parse_pattern(parts.next().ok_or_else(|| ParseError::missing("right pattern"))?)?;
            Ok(Pattern::Pair(Box::new(left), Box::new(right)))
        }
        Rule::wildcard_pattern => Ok(Pattern::Wildcard),
        Rule::literal_pattern => {
            let lit_pair = inner.into_inner().next().ok_or_else(|| ParseError::missing("literal"))?;
            let lit = parse_literal_value(lit_pair)?;
            Ok(Pattern::Literal(lit))
        }
        Rule::var_pattern => {
            let name = parse_identifier(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("var pattern"))?,
            );
            Ok(Pattern::Var(name))
        }
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected pattern rule: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_constructor_pattern(pair: pest::iterators::Pair<Rule>) -> Result<Pattern, ParseError> {
    let mut inner = pair.into_inner();

    let ctor = parse_constructor_name(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("constructor name"))?,
    );

    let mut args = Vec::new();
    for item in inner {
        match item.as_rule() {
            Rule::pattern_list => {
                for p in item.into_inner() {
                    if p.as_rule() == Rule::pattern {
                        args.push(parse_pattern(p)?);
                    }
                }
            }
            Rule::pattern => {
                args.push(parse_pattern(item)?);
            }
            _ => {}
        }
    }

    Ok(Pattern::Constructor { ctor, args })
}

// =========================================================================
// Binary operator parsing (produce surface AST)
// =========================================================================

fn parse_or_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_and_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("or_expr"))?)?;

    for right_pair in inner {
        let right = parse_and_expr(right_pair)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(left)
}

fn parse_and_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_eq_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("and_expr"))?)?;

    for right_pair in inner {
        let right = parse_eq_expr(right_pair)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(left)
}

fn parse_eq_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_cmp_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("eq_expr"))?)?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "==" => BinOp::Eq,
            "!=" => BinOp::Ne,
            _ => return Err(ParseError::Syntax {
                message: format!("Unknown eq op: {}", op_pair.as_str()),
                span: span_from_pair(&op_pair),
            }),
        };
        let right = parse_cmp_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp { op, left: Box::new(left), right: Box::new(right) },
            span,
        );
    }
    Ok(left)
}

fn parse_cmp_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_add_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("cmp_expr"))?)?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "<" => BinOp::Lt,
            "<=" => BinOp::Le,
            ">" => BinOp::Gt,
            ">=" => BinOp::Ge,
            _ => return Err(ParseError::Syntax {
                message: format!("Unknown cmp op: {}", op_pair.as_str()),
                span: span_from_pair(&op_pair),
            }),
        };
        let right = parse_add_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp { op, left: Box::new(left), right: Box::new(right) },
            span,
        );
    }
    Ok(left)
}

fn parse_add_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_mul_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("add_expr"))?)?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            _ => return Err(ParseError::Syntax {
                message: format!("Unknown add op: {}", op_pair.as_str()),
                span: span_from_pair(&op_pair),
            }),
        };
        let right = parse_mul_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp { op, left: Box::new(left), right: Box::new(right) },
            span,
        );
    }
    Ok(left)
}

fn parse_mul_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_unary_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("mul_expr"))?)?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,
            _ => return Err(ParseError::Syntax {
                message: format!("Unknown mul op: {}", op_pair.as_str()),
                span: span_from_pair(&op_pair),
            }),
        };
        let right = parse_unary_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp { op, left: Box::new(left), right: Box::new(right) },
            span,
        );
    }
    Ok(left)
}

fn parse_unary_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner().peekable();

    // Check for prefix operators
    if let Some(first) = inner.peek() {
        match first.as_str() {
            "!" => {
                inner.next();
                let operand = parse_unary_expr(inner.next().ok_or_else(|| ParseError::missing("operand"))?)?;
                return Ok(SurfaceExpr::new(
                    SurfaceExprKind::UnaryOp {
                        op: UnaryOp::Not,
                        operand: Box::new(operand),
                    },
                    span,
                ));
            }
            "-" => {
                inner.next();
                let operand = parse_unary_expr(inner.next().ok_or_else(|| ParseError::missing("operand"))?)?;
                return Ok(SurfaceExpr::new(
                    SurfaceExprKind::UnaryOp {
                        op: UnaryOp::Neg,
                        operand: Box::new(operand),
                    },
                    span,
                ));
            }
            _ => {}
        }
    }

    // Must be postfix_expr
    let next = inner.next().ok_or_else(|| ParseError::unexpected_end("unary"))?;
    parse_postfix_expr(next)
}

fn parse_postfix_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let base = parse_atom_expr(inner.next().ok_or_else(|| ParseError::unexpected_end("postfix"))?)?;

    let mut result = base;
    for op in inner {
        if op.as_rule() == Rule::postfix_op {
            let op_inner = op.into_inner().next().ok_or_else(|| ParseError::unexpected_end("postfix op"))?;
            match op_inner.as_rule() {
                Rule::call_op => {
                    let arg_pair = op_inner.into_inner().next().ok_or_else(|| ParseError::missing("call arg"))?;
                    let arg = parse_expression(arg_pair)?;
                    result = SurfaceExpr::new(
                        SurfaceExprKind::App {
                            func: Box::new(result),
                            arg: Box::new(arg),
                        },
                        span,
                    );
                }
                Rule::index_op => {
                    let idx_pair = op_inner.into_inner().next().ok_or_else(|| ParseError::missing("index"))?;
                    let index = parse_expression(idx_pair)?;
                    result = SurfaceExpr::new(
                        SurfaceExprKind::ListIndex {
                            list: Box::new(result),
                            index: Box::new(index),
                        },
                        span,
                    );
                }
                Rule::member_op => {
                    let member = op_inner.into_inner().next().ok_or_else(|| ParseError::missing("member"))?;
                    match member.as_rule() {
                        Rule::integer => {
                            let idx: usize = member.as_str().parse().map_err(|_| {
                                ParseError::Syntax {
                                    message: "Invalid tuple index".into(),
                                    span: span_from_pair(&member),
                                }
                            })?;
                            if idx == 0 {
                                result = SurfaceExpr::new(SurfaceExprKind::Fst(Box::new(result)), span);
                            } else if idx == 1 {
                                result = SurfaceExpr::new(SurfaceExprKind::Snd(Box::new(result)), span);
                            } else {
                                result = SurfaceExpr::new(
                                    SurfaceExprKind::TupleIndex {
                                        tuple: Box::new(result),
                                        index: idx,
                                    },
                                    span,
                                );
                            }
                        }
                        _ => {
                            // Field access — not yet in surface AST, treat as error
                            return Err(ParseError::Syntax {
                                message: "Named field access not yet supported".into(),
                                span: span_from_pair(&member),
                            });
                        }
                    }
                }
                _ => {}
            }
        }
    }

    Ok(result)
}

fn parse_atom_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("atom"))?;

    match inner.as_rule() {
        Rule::ffi_expr => {
            let mut parts = inner.into_inner();
            let symbol_pair = parts.next().ok_or_else(|| ParseError::missing("ffi symbol"))?;
            let symbol = parse_string_value(symbol_pair);
            let mut args = Vec::new();
            for p in parts {
                if p.as_rule() == Rule::expression {
                    args.push(parse_expression(p)?);
                }
            }
            Ok(SurfaceExpr::new(SurfaceExprKind::FFI { symbol, args }, span))
        }

        Rule::string_method => {
            let mut parts = inner.into_inner();
            let method = parse_identifier(parts.next().ok_or_else(|| ParseError::missing("method"))?);

            match method.as_str() {
                "new" => {
                    let mut region = SmolStr::default();
                    let mut value = String::new();
                    for p in parts {
                        match p.as_rule() {
                            Rule::identifier => region = parse_identifier(p),
                            Rule::expr_list => {
                                if let Some(arg) = p.into_inner().next() {
                                    if let Some(s) = arg.into_inner().next() {
                                        value = parse_string_value(s);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    Ok(SurfaceExpr::new(SurfaceExprKind::StringNew { region, value }, span))
                }
                "len" => {
                    let mut arg = None;
                    for p in parts {
                        if p.as_rule() == Rule::expr_list {
                            if let Some(first) = p.into_inner().next() {
                                arg = Some(parse_expression(first)?);
                            }
                        }
                    }
                    Ok(SurfaceExpr::new(
                        SurfaceExprKind::StringLen(Box::new(
                            arg.unwrap_or_else(|| SurfaceExpr::dummy(SurfaceExprKind::Lit(Literal::Unit))),
                        )),
                        span,
                    ))
                }
                _ => Err(ParseError::Syntax {
                    message: format!("Unknown string method: {}", method),
                    span,
                }),
            }
        }

        Rule::inl_expr => {
            let mut parts = inner.into_inner();
            let ty = parse_type(parts.next().ok_or_else(|| ParseError::missing("inl type"))?)?;
            let value = parse_expression(parts.next().ok_or_else(|| ParseError::missing("inl value"))?)?;
            Ok(SurfaceExpr::new(SurfaceExprKind::Inl { ty, value: Box::new(value) }, span))
        }

        Rule::inr_expr => {
            let mut parts = inner.into_inner();
            let ty = parse_type(parts.next().ok_or_else(|| ParseError::missing("inr type"))?)?;
            let value = parse_expression(parts.next().ok_or_else(|| ParseError::missing("inr value"))?)?;
            Ok(SurfaceExpr::new(SurfaceExprKind::Inr { ty, value: Box::new(value) }, span))
        }

        Rule::borrow_expr => {
            let inner_expr = parse_unary_expr(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("borrow"))?,
            )?;
            Ok(SurfaceExpr::new(SurfaceExprKind::Borrow(Box::new(inner_expr)), span))
        }

        Rule::drop_expr => {
            let inner_expr = parse_expression(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("drop"))?,
            )?;
            Ok(SurfaceExpr::new(SurfaceExprKind::Drop(Box::new(inner_expr)), span))
        }

        Rule::copy_expr => {
            let inner_expr = parse_expression(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("copy"))?,
            )?;
            Ok(SurfaceExpr::new(SurfaceExprKind::Copy(Box::new(inner_expr)), span))
        }

        Rule::construct_expr => parse_construct_expr(inner),

        Rule::list_literal => {
            let mut elements = Vec::new();
            for p in inner.into_inner() {
                if p.as_rule() == Rule::expression {
                    elements.push(parse_expression(p)?);
                }
            }
            Ok(SurfaceExpr::new(SurfaceExprKind::ListLit(elements), span))
        }

        Rule::paren_or_pair => {
            let mut exprs = Vec::new();
            for p in inner.into_inner() {
                if p.as_rule() == Rule::expression {
                    exprs.push(parse_expression(p)?);
                }
            }
            match exprs.len() {
                0 => Ok(SurfaceExpr::new(SurfaceExprKind::Lit(Literal::Unit), span)),
                1 => Ok(exprs.into_iter().next().unwrap()),
                2 => {
                    let mut iter = exprs.into_iter();
                    let left = iter.next().unwrap();
                    let right = iter.next().unwrap();
                    Ok(SurfaceExpr::new(
                        SurfaceExprKind::Pair {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                        span,
                    ))
                }
                _ => Ok(SurfaceExpr::new(SurfaceExprKind::TupleLit(exprs), span)),
            }
        }

        Rule::literal => {
            let lit_inner = inner
                .into_inner()
                .next()
                .ok_or_else(|| ParseError::unexpected_end("literal"))?;
            let lit = parse_literal_value(lit_inner)?;
            Ok(SurfaceExpr::new(SurfaceExprKind::Lit(lit), span))
        }

        Rule::variable => {
            let name = parse_identifier(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("variable name"))?,
            );
            Ok(SurfaceExpr::new(SurfaceExprKind::Var(name), span))
        }

        _ => Err(ParseError::Syntax {
            message: format!("Unexpected atom: {:?}", inner.as_rule()),
            span,
        }),
    }
}

fn parse_construct_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let ctor = parse_constructor_name(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("constructor name"))?,
    );

    let mut args = Vec::new();
    for item in inner {
        match item.as_rule() {
            Rule::expr_list => {
                for p in item.into_inner() {
                    if p.as_rule() == Rule::expression {
                        args.push(parse_expression(p)?);
                    }
                }
            }
            Rule::expression => {
                args.push(parse_expression(item)?);
            }
            _ => {}
        }
    }

    Ok(SurfaceExpr::new(
        SurfaceExprKind::Construct { ctor, args },
        span,
    ))
}

// =========================================================================
// Literal parsing
// =========================================================================

fn parse_literal_value(pair: pest::iterators::Pair<Rule>) -> Result<Literal, ParseError> {
    match pair.as_rule() {
        Rule::unit_literal => Ok(Literal::Unit),
        Rule::boolean => match pair.as_str() {
            "true" => Ok(Literal::Bool(true)),
            "false" => Ok(Literal::Bool(false)),
            _ => Err(ParseError::Syntax {
                message: format!("Invalid boolean: {}", pair.as_str()),
                span: span_from_pair(&pair),
            }),
        },
        Rule::integer => {
            let n: i32 = pair.as_str().parse().map_err(|_| ParseError::Syntax {
                message: format!("Invalid integer: {}", pair.as_str()),
                span: span_from_pair(&pair),
            })?;
            Ok(Literal::I32(n))
        }
        Rule::float => {
            let f: f64 = pair.as_str().parse().map_err(|_| ParseError::Syntax {
                message: format!("Invalid float: {}", pair.as_str()),
                span: span_from_pair(&pair),
            })?;
            Ok(Literal::F64(f))
        }
        Rule::string => {
            let s = parse_string_value(pair);
            Ok(Literal::String(s))
        }
        _ => {
            // Try going one level deeper (literal wraps the actual value)
            if let Some(inner) = pair.into_inner().next() {
                parse_literal_value(inner)
            } else {
                Err(ParseError::Syntax {
                    message: "Empty literal".into(),
                    span: Span::dummy(),
                })
            }
        }
    }
}

fn parse_string_value(pair: pest::iterators::Pair<Rule>) -> String {
    let raw = pair.as_str();
    // Strip quotes
    let inner = &raw[1..raw.len() - 1];
    // Unescape
    inner
        .replace("\\n", "\n")
        .replace("\\r", "\r")
        .replace("\\t", "\t")
        .replace("\\\\", "\\")
        .replace("\\\"", "\"")
}

// =========================================================================
// Type parsing (surface types)
// =========================================================================

fn parse_type(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceTy, ParseError> {
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| ParseError::unexpected_end("type"))?;

    let left = parse_sum_ty(first)?;

    // Check for function arrow
    if let Some(ret) = inner.next() {
        let ret_ty = parse_type(ret)?;
        Ok(SurfaceTy::Fun {
            param: Box::new(left),
            ret: Box::new(ret_ty),
        })
    } else {
        Ok(left)
    }
}

fn parse_sum_ty(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceTy, ParseError> {
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .ok_or_else(|| ParseError::unexpected_end("sum type"))?;
    let mut left = parse_type_atom(first)?;

    for right_pair in inner {
        let right = parse_type_atom(right_pair)?;
        left = SurfaceTy::Sum {
            left: Box::new(left),
            right: Box::new(right),
        };
    }

    Ok(left)
}

fn parse_type_atom(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceTy, ParseError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("type atom"))?;

    match inner.as_rule() {
        Rule::base_ty => parse_base_ty(inner),
        Rule::string_ty => {
            let region = inner
                .into_inner()
                .find(|p| p.as_rule() == Rule::identifier)
                .map(|p| parse_identifier(p))
                .unwrap_or_else(|| SmolStr::new("_"));
            Ok(SurfaceTy::String(region))
        }
        Rule::borrow_ty => {
            let inner_ty = parse_type_atom(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("borrow inner"))?,
            )?;
            Ok(SurfaceTy::Borrow(Box::new(inner_ty)))
        }
        Rule::list_ty => {
            let elem_ty = parse_type(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("list element type"))?,
            )?;
            Ok(SurfaceTy::List(Box::new(elem_ty)))
        }
        Rule::product_ty => {
            let tys: Vec<SurfaceTy> = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::ty)
                .map(parse_type)
                .collect::<Result<_, _>>()?;
            Ok(SurfaceTy::Tuple(tys))
        }
        Rule::named_ty => {
            let mut parts = inner.into_inner();
            let name = parse_constructor_name(
                parts.next().ok_or_else(|| ParseError::missing("type name"))?,
            );
            let mut args = Vec::new();
            for p in parts {
                match p.as_rule() {
                    Rule::ty_list => {
                        for ty_p in p.into_inner() {
                            if ty_p.as_rule() == Rule::ty {
                                args.push(parse_type(ty_p)?);
                            }
                        }
                    }
                    Rule::ty => args.push(parse_type(p)?),
                    _ => {}
                }
            }
            Ok(SurfaceTy::Named { name, args })
        }
        Rule::type_var => {
            let name = parse_identifier(
                inner.into_inner().next().ok_or_else(|| ParseError::missing("type var"))?,
            );
            Ok(SurfaceTy::Var(name))
        }
        Rule::record_ty => {
            // Records not yet in surface AST — parse as error for now
            Err(ParseError::Syntax {
                message: "Record types not yet supported in surface AST".into(),
                span: span_from_pair(&inner),
            })
        }
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected type atom: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_base_ty(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceTy, ParseError> {
    let inner = pair
        .into_inner()
        .next()
        .map(|p| p.as_str().to_string())
        .unwrap_or_default();

    match inner.as_str() {
        "()" | "" => Ok(SurfaceTy::Base(BaseTy::Unit)),
        "Bool" => Ok(SurfaceTy::Base(BaseTy::Bool)),
        "I32" => Ok(SurfaceTy::Base(BaseTy::I32)),
        "I64" => Ok(SurfaceTy::Base(BaseTy::I64)),
        "F32" => Ok(SurfaceTy::Base(BaseTy::F32)),
        "F64" => Ok(SurfaceTy::Base(BaseTy::F64)),
        _ => {
            // base_ty matched but text doesn't match any — check the pair text
            Ok(SurfaceTy::Base(BaseTy::Unit))
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_data_declaration() {
        let source = "data Option(a) = None | Some(a)";
        let module = parse_surface_module(source, "test").unwrap();
        assert_eq!(module.decls.len(), 1);
        if let SurfaceDecl::Data(d) = &module.decls[0] {
            assert_eq!(d.name.as_str(), "Option");
            assert_eq!(d.params.len(), 1);
            assert_eq!(d.constructors.len(), 2);
            assert_eq!(d.constructors[0].name.as_str(), "None");
            assert_eq!(d.constructors[1].name.as_str(), "Some");
        } else {
            panic!("expected Data decl");
        }
    }

    #[test]
    fn parse_data_no_params() {
        let source = "data Color = Red | Green | Blue";
        let module = parse_surface_module(source, "test").unwrap();
        if let SurfaceDecl::Data(d) = &module.decls[0] {
            assert_eq!(d.name.as_str(), "Color");
            assert!(d.params.is_empty());
            assert_eq!(d.constructors.len(), 3);
        } else {
            panic!("expected Data decl");
        }
    }

    #[test]
    fn parse_construct_nullary() {
        let source = "None";
        let expr = parse_surface_expr(source).unwrap();
        assert!(matches!(expr.kind, SurfaceExprKind::Construct { .. }));
    }

    #[test]
    fn parse_construct_with_arg() {
        let source = "Some(42)";
        let expr = parse_surface_expr(source).unwrap();
        if let SurfaceExprKind::Construct { ctor, args } = &expr.kind {
            assert_eq!(ctor.as_str(), "Some");
            assert_eq!(args.len(), 1);
        } else {
            panic!("expected Construct");
        }
    }

    #[test]
    fn parse_match_expression() {
        let source = r#"match x of
            | None => 0
            | Some(v) => v
            end"#;
        let expr = parse_surface_expr(source).unwrap();
        if let SurfaceExprKind::Match { arms, .. } = &expr.kind {
            assert_eq!(arms.len(), 2);
        } else {
            panic!("expected Match");
        }
    }

    #[test]
    fn parse_match_with_wildcard() {
        let source = r#"match c of
            | Red => 1
            | _ => 0
            end"#;
        // Need Color data type registered for Red to parse as constructor
        // But Red is an uppercase identifier, so it parses as construct_expr
        let expr = parse_surface_expr(source).unwrap();
        assert!(matches!(expr.kind, SurfaceExprKind::Match { .. }));
    }

    #[test]
    fn parse_named_type() {
        let source = "fn unwrap(x: Option(I32)): I32 = x";
        let module = parse_surface_module(source, "test").unwrap();
        if let SurfaceDecl::Fn { params, .. } = &module.decls[0] {
            assert!(matches!(&params[0].1, SurfaceTy::Named { .. }));
        }
    }

    #[test]
    fn parse_existing_let_expr() {
        let source = "let x = 42 in x";
        let expr = parse_surface_expr(source).unwrap();
        assert!(matches!(expr.kind, SurfaceExprKind::Let { .. }));
    }

    #[test]
    fn parse_existing_let_lin_expr() {
        let source = "let! x = 42 in x";
        let expr = parse_surface_expr(source).unwrap();
        assert!(matches!(expr.kind, SurfaceExprKind::LetLin { .. }));
    }

    #[test]
    fn parse_full_module_with_data_and_match() {
        let source = r#"
            data Option(a) = None | Some(a)

            fn unwrap_or(opt: Option(I32), default: I32): I32 =
                match opt of
                | None => default
                | Some(v) => v
                end
        "#;
        let module = parse_surface_module(source, "test").unwrap();
        assert_eq!(module.decls.len(), 2);
        assert!(matches!(&module.decls[0], SurfaceDecl::Data(_)));
        assert!(matches!(&module.decls[1], SurfaceDecl::Fn { .. }));
    }
}
