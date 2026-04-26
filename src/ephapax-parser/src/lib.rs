#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
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

use ephapax_syntax::{
    BaseTy, BinOp, Decl, Expr, ExprKind, Import, Literal, Module, Span, Ty, UnaryOp, Visibility,
};
use pest::Parser;
use pest_derive::Parser;
use smol_str::SmolStr;

pub mod error;
pub mod surface;

pub use error::{ParseError, Report};
pub use surface::{parse_surface_expr, parse_surface_module};

#[derive(Parser)]
#[grammar = "ephapax.pest"]
struct EphapaxParser;

/// Parse source code into an expression
pub fn parse(source: &str) -> Result<Expr, Vec<ParseError>> {
    let pairs = EphapaxParser::parse(Rule::expression_only, source).map_err(|e| {
        vec![ParseError::Syntax {
            message: e.to_string(),
            span: Span::dummy(),
        }]
    })?;

    let pair = pairs
        .into_iter()
        .next()
        .ok_or_else(|| vec![ParseError::unexpected_end("top-level expression")])?;
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| vec![ParseError::unexpected_end("inner expression")])?;

    parse_expression(inner).map_err(|e| vec![e])
}

/// Parse source code into a module (multiple declarations)
pub fn parse_module(source: &str, name: &str) -> Result<Module, Vec<ParseError>> {
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
    let mut imports = Vec::new();
    let mut module_name = SmolStr::new(name);

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::module_decl => {
                // Extract qualified name from `module Foo.Bar.Baz`
                if let Some(qn) = inner.into_inner().next() {
                    module_name = SmolStr::new(qn.as_str());
                }
            }
            Rule::declaration => {
                decls.push(parse_declaration(inner).map_err(|e| vec![e])?);
            }
            Rule::import_decl => {
                imports.push(parse_import(inner).map_err(|e| vec![e])?);
            }
            _ => {} // SOI, EOI
        }
    }

    Ok(Module {
        name: module_name,
        imports,
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

fn parse_import(pair: pest::iterators::Pair<Rule>) -> Result<Import, ParseError> {
    let mut inner = pair.into_inner();
    let module_name_pair = inner
        .next()
        .ok_or_else(|| ParseError::missing("module name"))?;

    // Module name is now a qualified_name (e.g., "GSA.Core.Types")
    let module_name = SmolStr::new(module_name_pair.as_str());

    let mut names = Vec::new();
    for item in inner {
        if item.as_rule() == Rule::identifier {
            names.push(parse_identifier(item));
        }
    }

    Ok(Import {
        module: module_name,
        names,
    })
}

fn parse_declaration(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("declaration"))?;

    match inner.as_rule() {
        Rule::fn_decl => parse_fn_decl(inner),
        Rule::type_decl => parse_type_decl(inner),
        Rule::data_decl => parse_type_decl(inner), // data decls are a form of type decl
        Rule::const_decl => parse_const_decl(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected declaration: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_fn_decl(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let inner = pair.into_inner();

    let mut visibility = Visibility::Private;
    let mut type_params = Vec::new();
    let mut name = None;
    let mut params = Vec::new();
    let mut ret_ty = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::visibility => {
                visibility = Visibility::Public;
            }
            Rule::identifier if name.is_none() => {
                name = Some(parse_identifier(item));
            }
            Rule::fn_type_params => {
                for tp in item.into_inner() {
                    if tp.as_rule() == Rule::identifier {
                        type_params.push(parse_identifier(tp));
                    }
                }
            }
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

    Ok(Decl::Fn {
        name: name.unwrap_or_else(|| SmolStr::new("_")),
        visibility,
        type_params,
        params,
        ret_ty: ret_ty.unwrap_or(Ty::Base(BaseTy::Unit)),
        body: body.unwrap_or_else(|| Expr::dummy(ExprKind::Lit(Literal::Unit))),
    })
}

fn parse_const_decl(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let mut inner = pair.into_inner();
    let mut name = None;
    let mut ty = None;
    let mut value = None;

    for item in &mut inner {
        match item.as_rule() {
            Rule::identifier if name.is_none() => {
                name = Some(parse_identifier(item));
            }
            Rule::ty => {
                ty = Some(parse_type(item)?);
            }
            Rule::expression => {
                value = Some(parse_expression(item)?);
            }
            _ => {}
        }
    }

    Ok(Decl::Const {
        name: name.unwrap_or_else(|| SmolStr::new("_")),
        ty,
        value: value.unwrap_or_else(|| Expr::dummy(ExprKind::Lit(Literal::Unit))),
    })
}

fn parse_type_decl(pair: pest::iterators::Pair<Rule>) -> Result<Decl, ParseError> {
    let mut inner = pair.into_inner();
    let mut visibility = Visibility::Private;
    let mut name = None;

    for item in &mut inner {
        match item.as_rule() {
            Rule::visibility => {
                visibility = Visibility::Public;
            }
            Rule::linearity => {
                // Record linearity for future use (type system)
                // For now, just skip it during parsing
            }
            Rule::identifier => {
                name = Some(parse_identifier(item));
                break;
            }
            _ => {}
        }
    }

    let name = name.ok_or_else(|| ParseError::missing("type name"))?;

    let ty_or_def = inner
        .next()
        .ok_or_else(|| ParseError::missing("type definition"))?;
    let ty = match ty_or_def.as_rule() {
        Rule::sum_type_def => parse_sum_type_def(ty_or_def)?,
        Rule::record_type_def => parse_record_type_def(ty_or_def)?,
        Rule::named_record_type_def => parse_record_type_def(ty_or_def)?, // constructor name skipped
        Rule::ty => parse_type(ty_or_def)?,
        _ => {
            return Err(ParseError::Syntax {
                message: format!(
                    "Expected type or type definition, got {:?}",
                    ty_or_def.as_rule()
                ),
                span: Span::dummy(),
            })
        }
    };

    Ok(Decl::Type { name, visibility, ty })
}

fn parse_sum_type_def(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    let variants: Vec<_> = pair.into_inner().collect();

    if variants.is_empty() {
        return Err(ParseError::Syntax {
            message: "Sum type must have at least one variant".to_string(),
            span: Span::dummy(),
        });
    }

    // Parse each variant
    let mut variant_types = Vec::new();
    for variant_pair in variants {
        let mut inner = variant_pair.into_inner();
        let _variant_name = parse_identifier(
            inner
                .next()
                .ok_or_else(|| ParseError::missing("variant name"))?,
        );

        // For now, treat each variant as a unit type
        // In the future, we could parse the optional type parameter
        let ty = if let Some(ty_pair) = inner.next() {
            parse_type(ty_pair)?
        } else {
            Ty::Base(BaseTy::Unit)
        };

        variant_types.push(ty);
    }

    // Build nested sum type: A + (B + (C + ...))
    let mut result = variant_types[0].clone();
    for variant_ty in &variant_types[1..] {
        result = Ty::Sum {
            left: Box::new(result),
            right: Box::new(variant_ty.clone()),
        };
    }

    Ok(result)
}

fn parse_record_type_def(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    // For now, represent records as nested products
    let mut field_types = Vec::new();

    for field_pair in pair.into_inner() {
        let mut inner = field_pair.into_inner();
        let _field_name = parse_identifier(
            inner
                .next()
                .ok_or_else(|| ParseError::missing("field name"))?,
        );
        let field_ty = parse_type(
            inner
                .next()
                .ok_or_else(|| ParseError::missing("field type"))?,
        )?;
        field_types.push(field_ty);
    }

    if field_types.is_empty() {
        return Ok(Ty::Base(BaseTy::Unit));
    }

    // Build nested product: (A, B, C, ...) using Tuple
    Ok(Ty::Tuple(field_types))
}

// ============================================================================
// Type Parsing
// ============================================================================

fn parse_type(pair: pest::iterators::Pair<Rule>) -> Result<Ty, ParseError> {
    let mut inner = pair.into_inner().peekable();

    let first = inner.next().ok_or_else(|| ParseError::missing("type"))?;
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
    let mut result = parse_type_atom(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("sum type component"))?,
    )?;

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
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::missing("type atom"))?;

    match inner.as_rule() {
        Rule::base_ty => parse_base_type(inner),
        Rule::string_ty => {
            let region = inner
                .into_inner()
                .next()
                .map(parse_identifier)
                .unwrap_or_else(|| SmolStr::from("default"));
            Ok(Ty::String(region))
        }
        Rule::borrow_ty => {
            let inner_ty = parse_type_atom(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("borrowed type"))?,
            )?;
            Ok(Ty::Borrow(Box::new(inner_ty)))
        }
        Rule::list_ty => {
            let elem_ty = parse_type(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("list element type"))?,
            )?;
            Ok(Ty::List(Box::new(elem_ty)))
        }
        Rule::product_ty => {
            let mut types: Vec<Ty> = Vec::new();
            for ty_pair in inner.into_inner() {
                types.push(parse_type(ty_pair)?);
            }

            if types.len() == 1 {
                // SAFETY: len() == 1 guarantees next() returns Some
                Ok(types
                    .into_iter()
                    .next()
                    .ok_or_else(|| ParseError::missing("product type element"))?)
            } else {
                let result = types.into_iter().reduce(|acc, t| Ty::Prod {
                    left: Box::new(acc),
                    right: Box::new(t),
                });
                // SAFETY: reduce on non-empty iterator always returns Some
                Ok(result.ok_or_else(|| ParseError::missing("product type"))?)
            }
        }
        Rule::type_var => {
            let name = parse_identifier(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("type variable name"))?,
            );
            Ok(Ty::Var(name))
        }
        Rule::named_ty => {
            // In the core parser, named types without arguments are type variables.
            // Named types with arguments (like Option(I32)) are handled by the
            // surface parser and desugared to binary sums.
            let mut parts = inner.into_inner();
            let name = parts
                .next()
                .ok_or_else(|| ParseError::missing("named type name"))?;
            let name_str = SmolStr::new(name.as_str());

            if parts.next().is_some() {
                // Has arguments — not supported in core parser
                return Err(ParseError::Syntax {
                    message: format!("Parameterized type '{}(...)' requires the surface parser", name_str),
                    span: span_from_pair(&name),
                });
            }

            // Bare name — treat as type variable
            Ok(Ty::Var(name_str))
        }
        Rule::record_ty => {
            // Parse as tuple of field types
            let mut field_types = Vec::new();
            for field_pair in inner.into_inner() {
                let mut field_inner = field_pair.into_inner();
                let _field_name = parse_identifier(
                    field_inner
                        .next()
                        .ok_or_else(|| ParseError::missing("record field name"))?,
                );
                let field_ty = parse_type(
                    field_inner
                        .next()
                        .ok_or_else(|| ParseError::missing("record field type"))?,
                )?;
                field_types.push(field_ty);
            }
            Ok(Ty::Tuple(field_types))
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
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("expression"))?;

    match inner.as_rule() {
        Rule::seq_expr => parse_seq_expr_core(inner),
        Rule::single_expr => parse_single_expr_core(inner),
        Rule::let_expr => parse_let_expr(inner),
        Rule::let_lin_expr => parse_let_lin_expr(inner),
        Rule::lambda_expr => parse_lambda_expr(inner),
        Rule::if_expr => parse_if_expr(inner),
        Rule::region_expr => parse_region_expr(inner),
        Rule::case_expr => parse_case_expr(inner),
        Rule::handle_expr => parse_handle_expr(inner),
        Rule::or_expr => parse_or_expr(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected expression: {:?}", inner.as_rule()),
            span,
        }),
    }
}

/// Parse semicolon-separated expression sequence (core AST).
///
/// `e1 ; e2 ; e3` desugars to `let _ = e1 in let _ = e2 in e3`.
fn parse_seq_expr_core(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let exprs: Vec<_> = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::single_expr)
        .collect();

    if exprs.is_empty() {
        return Ok(Expr::new(ExprKind::Lit(Literal::Unit), span));
    }

    let mut parsed: Vec<Expr> = Vec::with_capacity(exprs.len());
    for e in exprs {
        parsed.push(parse_single_expr_core(e)?);
    }

    if parsed.len() == 1 {
        // invariant: len() == 1 guarantees next() returns Some
        return Ok(parsed.into_iter().next().expect("invariant: parsed.len() == 1"));
    }

    // invariant: loop above ensures parsed is not empty before we enter this block
    let last = parsed.pop().expect("invariant: parsed is not empty");
    parsed.into_iter().rev().fold(Ok(last), |acc, expr| {
        let acc = acc?;
        let s = expr.span;
        Ok(Expr::new(
            ExprKind::Let {
                name: SmolStr::new("_"),
                ty: None,
                value: Box::new(expr),
                body: Box::new(acc),
            },
            s,
        ))
    })
}

/// Parse a single (non-sequenced) expression in the core AST.
fn parse_single_expr_core(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("single expression"))?;

    match inner.as_rule() {
        Rule::let_expr => parse_let_expr(inner),
        Rule::let_lin_expr => parse_let_lin_expr(inner),
        Rule::lambda_expr => parse_lambda_expr(inner),
        Rule::if_expr => parse_if_expr(inner),
        Rule::region_expr => parse_region_expr(inner),
        Rule::case_expr => parse_case_expr(inner),
        Rule::handle_expr => parse_handle_expr(inner),
        Rule::or_expr => parse_or_expr(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected single_expr: {:?}", inner.as_rule()),
            span,
        }),
    }
}

fn parse_let_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("let binding name"))?,
    );

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
            value: Box::new(value.ok_or_else(|| ParseError::missing("let binding value"))?),
            body: Box::new(body.ok_or_else(|| ParseError::missing("let binding body"))?),
        },
        span,
    ))
}

fn parse_let_lin_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let name = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("let-lin binding name"))?,
    );

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
            value: Box::new(value.ok_or_else(|| ParseError::missing("let-lin binding value"))?),
            body: Box::new(body.ok_or_else(|| ParseError::missing("let-lin binding body"))?),
        },
        span,
    ))
}

fn parse_lambda_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let param = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("lambda parameter name"))?,
    );
    let param_ty = parse_type(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("lambda parameter type"))?,
    )?;
    let body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("lambda body"))?,
    )?;

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

    let cond = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("if condition"))?,
    )?;
    let then_branch = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("if then-branch"))?,
    )?;
    let else_branch = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("if else-branch"))?,
    )?;

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

    let name = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("region name"))?,
    );
    let body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("region body"))?,
    )?;

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

    let scrutinee = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("case scrutinee"))?,
    )?;
    let left_var = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("case left variable"))?,
    );
    let left_body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("case left body"))?,
    )?;
    let right_var = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("case right variable"))?,
    );
    let right_body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("case right body"))?,
    )?;

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

fn parse_handle_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    use ephapax_syntax::{HandlerClause, ResumeMode};

    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    // First child is the body expression
    let body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("handle body"))?,
    )?;

    // Remaining children are handler_clause
    let mut clauses = Vec::new();
    for clause_pair in inner {
        if clause_pair.as_rule() != Rule::handler_clause {
            continue;
        }
        let clause_inner = clause_pair
            .into_inner()
            .next()
            .ok_or_else(|| ParseError::missing("handler clause content"))?;

        match clause_inner.as_rule() {
            Rule::handler_return_clause => {
                let mut parts = clause_inner.into_inner();
                let param = parse_identifier(
                    parts
                        .next()
                        .ok_or_else(|| ParseError::missing("return param"))?,
                );
                let body = parse_expression(
                    parts
                        .next()
                        .ok_or_else(|| ParseError::missing("return body"))?,
                )?;
                clauses.push(HandlerClause {
                    op: SmolStr::default(), // empty = return clause
                    params: vec![param],
                    resume_mode: None,
                    body,
                });
            }
            Rule::handler_op_clause => {
                let mut parts = clause_inner.into_inner();
                let op = parse_identifier(
                    parts
                        .next()
                        .ok_or_else(|| ParseError::missing("handler op name"))?,
                );

                let mut params = Vec::new();
                let mut resume_mode = None;
                let mut body_expr = None;

                for item in parts {
                    match item.as_rule() {
                        Rule::handler_param_list => {
                            for param_item in item.into_inner() {
                                match param_item.as_rule() {
                                    Rule::handler_param => {
                                        let hp_inner = param_item.into_inner().next();
                                        if let Some(hp) = hp_inner {
                                            match hp.as_rule() {
                                                Rule::resume_param => {
                                                    // Check for mode
                                                    if let Some(mode_pair) = hp.into_inner().next()
                                                    {
                                                        resume_mode =
                                                            Some(match mode_pair.as_str() {
                                                                "once" => ResumeMode::Once,
                                                                "multi" => ResumeMode::Multi,
                                                                _ => ResumeMode::Once,
                                                            });
                                                    } else {
                                                        resume_mode = Some(ResumeMode::Once); // default
                                                    }
                                                }
                                                Rule::identifier => {
                                                    params.push(parse_identifier(hp));
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        Rule::expression => {
                            body_expr = Some(parse_expression(item)?);
                        }
                        _ => {}
                    }
                }

                clauses.push(HandlerClause {
                    op,
                    params,
                    resume_mode,
                    body: body_expr
                        .unwrap_or_else(|| Expr::dummy(ExprKind::Lit(Literal::Unit))),
                });
            }
            _ => {}
        }
    }

    Ok(Expr::new(
        ExprKind::Handle {
            body: Box::new(body),
            clauses,
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

    let mut result = parse_and_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("or expression"))?,
    )?;

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

    let mut result = parse_eq_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("and expression"))?,
    )?;

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

    let mut result = parse_cmp_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("equality expression"))?,
    )?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::eq_op {
            let op = match next.as_str() {
                "==" => BinOp::Eq,
                "!=" => BinOp::Ne,
                _ => unreachable!(),
            };
            (
                op,
                inner
                    .next()
                    .ok_or_else(|| ParseError::missing("right-hand side of equality"))?,
            )
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

    let mut result = parse_add_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("comparison expression"))?,
    )?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::cmp_op {
            let op = match next.as_str() {
                "<" => BinOp::Lt,
                ">" => BinOp::Gt,
                "<=" => BinOp::Le,
                ">=" => BinOp::Ge,
                _ => unreachable!(),
            };
            (
                op,
                inner
                    .next()
                    .ok_or_else(|| ParseError::missing("right-hand side of comparison"))?,
            )
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

    let mut result = parse_mul_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("additive expression"))?,
    )?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::add_op {
            let op = match next.as_str() {
                "+" => BinOp::Add,
                "-" => BinOp::Sub,
                _ => unreachable!(),
            };
            (
                op,
                inner
                    .next()
                    .ok_or_else(|| ParseError::missing("right-hand side of addition"))?,
            )
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

    let mut result = parse_unary_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("multiplicative expression"))?,
    )?;

    while let Some(next) = inner.next() {
        let (op, right_pair) = if next.as_rule() == Rule::mul_op {
            let op = match next.as_str() {
                "*" => BinOp::Mul,
                "/" => BinOp::Div,
                "%" => BinOp::Mod,
                _ => unreachable!(),
            };
            (
                op,
                inner
                    .next()
                    .ok_or_else(|| ParseError::missing("right-hand side of multiplication"))?,
            )
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
        let inner = pair
            .into_inner()
            .next()
            .ok_or_else(|| ParseError::missing("unary not operand"))?;
        let operand = parse_unary_expr(inner)?;
        Ok(Expr::new(
            ExprKind::UnaryOp {
                op: UnaryOp::Not,
                operand: Box::new(operand),
            },
            span,
        ))
    } else if text.starts_with('-') && !text.chars().nth(1).is_some_and(|c| c.is_ascii_digit()) {
        let inner = pair
            .into_inner()
            .next()
            .ok_or_else(|| ParseError::missing("unary negation operand"))?;
        let operand = parse_unary_expr(inner)?;
        Ok(Expr::new(
            ExprKind::UnaryOp {
                op: UnaryOp::Neg,
                operand: Box::new(operand),
            },
            span,
        ))
    } else {
        let inner = pair
            .into_inner()
            .next()
            .ok_or_else(|| ParseError::unexpected_end("unary expression"))?;
        parse_postfix_expr(inner)
    }
}

fn parse_postfix_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut result = parse_atom_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("postfix expression"))?,
    )?;

    for op in inner {
        if op.as_rule() == Rule::postfix_op {
            let op_inner = op
                .into_inner()
                .next()
                .ok_or_else(|| ParseError::unexpected_end("postfix operator"))?;
            match op_inner.as_rule() {
                Rule::call_op => {
                    let call_inner: Vec<_> = op_inner.into_inner().collect();
                    if call_inner.is_empty() {
                        // Zero-arg call: foo() → App(foo, ())
                        result = Expr::new(
                            ExprKind::App {
                                func: Box::new(result),
                                arg: Box::new(Expr::new(
                                    ExprKind::Lit(Literal::Unit),
                                    span,
                                )),
                            },
                            span,
                        );
                    } else {
                        // call_args: one or more comma-separated expressions
                        let arg_exprs: Vec<_> = call_inner[0]
                            .clone()
                            .into_inner()
                            .filter(|p| p.as_rule() == Rule::expression)
                            .collect();
                        // Curry: f(a, b, c) → App(App(App(f, a), b), c)
                        for arg_pair in arg_exprs {
                            let arg = parse_expression(arg_pair)?;
                            result = Expr::new(
                                ExprKind::App {
                                    func: Box::new(result),
                                    arg: Box::new(arg),
                                },
                                span,
                            );
                        }
                    }
                }
                Rule::index_op => {
                    let index = parse_expression(
                        op_inner
                            .into_inner()
                            .next()
                            .ok_or_else(|| ParseError::missing("index expression"))?,
                    )?;
                    result = Expr::new(
                        ExprKind::ListIndex {
                            list: Box::new(result),
                            index: Box::new(index),
                        },
                        span,
                    );
                }
                Rule::member_op => {
                    let member = op_inner
                        .into_inner()
                        .next()
                        .ok_or_else(|| ParseError::missing("member access target"))?;
                    match member.as_rule() {
                        Rule::integer => {
                            let index = member.as_str().parse::<usize>().map_err(|_| {
                                ParseError::Syntax {
                                    message: format!("Invalid tuple index: {}", member.as_str()),
                                    span: span_from_pair(&member),
                                }
                            })?;
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
    }

    Ok(result)
}

fn parse_atom_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("atom expression"))?;

    match inner.as_rule() {
        Rule::perform_expr => {
            let mut parts = inner.into_inner();
            let op = parse_identifier(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("effect operation name"))?,
            );
            let mut args = Vec::new();
            for arg_pair in parts {
                if arg_pair.as_rule() == Rule::expression || arg_pair.as_rule() == Rule::expr_list
                {
                    for expr_pair in arg_pair.into_inner() {
                        if expr_pair.as_rule() == Rule::expression {
                            args.push(parse_expression(expr_pair)?);
                        }
                    }
                }
            }
            Ok(Expr::new(ExprKind::Perform { op, args }, span))
        }
        Rule::ffi_expr => {
            let mut parts = inner.into_inner();
            // First arg is the symbol name (a string literal)
            let symbol_pair = parts
                .next()
                .ok_or_else(|| ParseError::missing("FFI symbol name"))?;
            let symbol = symbol_pair.as_str().trim_matches('"').to_string();
            // Remaining args are expressions
            let mut args = Vec::new();
            for arg_pair in parts {
                if arg_pair.as_rule() == Rule::expression {
                    args.push(parse_expression(arg_pair)?);
                }
            }
            Ok(Expr::new(ExprKind::FFI { symbol, args }, span))
        }
        Rule::string_method => parse_string_method(inner),
        Rule::inl_expr => {
            let mut parts = inner.into_inner();
            let ty = parse_type(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("inl type"))?,
            )?;
            let value = parse_expression(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("inl value"))?,
            )?;
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
            let ty = parse_type(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("inr type"))?,
            )?;
            let value = parse_expression(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("inr value"))?,
            )?;
            Ok(Expr::new(
                ExprKind::Inr {
                    ty,
                    value: Box::new(value),
                },
                span,
            ))
        }
        Rule::borrow_expr => {
            let inner_expr = parse_unary_expr(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("borrow operand"))?,
            )?;
            Ok(Expr::new(ExprKind::Borrow(Box::new(inner_expr)), span))
        }
        Rule::fst_expr => {
            let inner_expr = parse_expression(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("fst operand"))?,
            )?;
            Ok(Expr::new(ExprKind::Fst(Box::new(inner_expr)), span))
        }
        Rule::snd_expr => {
            let inner_expr = parse_expression(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("snd operand"))?,
            )?;
            Ok(Expr::new(ExprKind::Snd(Box::new(inner_expr)), span))
        }
        Rule::drop_expr => {
            let inner_expr = parse_expression(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("drop operand"))?,
            )?;
            Ok(Expr::new(ExprKind::Drop(Box::new(inner_expr)), span))
        }
        Rule::copy_expr => {
            let inner_expr = parse_expression(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("copy operand"))?,
            )?;
            Ok(Expr::new(ExprKind::Copy(Box::new(inner_expr)), span))
        }
        Rule::record_literal => {
            // Parse as tuple literal (field values in order)
            let mut field_values = Vec::new();
            for field_assign_pair in inner.into_inner() {
                let mut field_inner = field_assign_pair.into_inner();
                let _field_name = parse_identifier(
                    field_inner
                        .next()
                        .ok_or_else(|| ParseError::missing("record field name"))?,
                );

                // Skip optional type annotation
                let value_pair = field_inner
                    .next()
                    .ok_or_else(|| ParseError::missing("record field value"))?;
                let value = if value_pair.as_rule() == Rule::ty {
                    // Has type annotation, next is expression
                    parse_expression(
                        field_inner
                            .next()
                            .ok_or_else(|| ParseError::missing("record field expression"))?,
                    )?
                } else {
                    // No type annotation, this is the expression
                    parse_expression(value_pair)?
                };

                field_values.push(value);
            }
            Ok(Expr::new(ExprKind::TupleLit(field_values), span))
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
            let name = parse_identifier(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("variable name"))?,
            );
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

    let method = parse_identifier(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("string method name"))?,
    );

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
        1 => {
            // SAFETY: match arm guarantees len() == 1, so next() returns Some
            Ok(exprs
                .into_iter()
                .next()
                .ok_or_else(|| ParseError::unexpected_end("parenthesized expression"))?)
        }
        2 => {
            // Keep using Pair for 2-element tuples for backward compatibility
            let mut iter = exprs.into_iter();
            // SAFETY: match arm guarantees len() == 2
            let left = iter
                .next()
                .ok_or_else(|| ParseError::unexpected_end("pair left"))?;
            let right = iter
                .next()
                .ok_or_else(|| ParseError::unexpected_end("pair right"))?;
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
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("literal"))?;

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
            let content = &s[1..s.len() - 1];
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

    // ===== New feature parsing tests =====

    #[test]
    fn test_parse_pub_fn() {
        let source = r#"pub fn double(x: I32): I32 = x"#;
        let module = parse_module(source, "test").expect("should parse");
        assert_eq!(module.decls.len(), 1);
        match &module.decls[0] {
            Decl::Fn { name, visibility, .. } => {
                assert_eq!(name.as_str(), "double");
                assert_eq!(*visibility, Visibility::Public);
            }
            other => panic!("Expected Fn decl, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_private_fn_default() {
        let source = r#"fn secret(x: I32): I32 = x"#;
        let module = parse_module(source, "test").expect("should parse");
        match &module.decls[0] {
            Decl::Fn { visibility, .. } => {
                assert_eq!(*visibility, Visibility::Private);
            }
            other => panic!("Expected Fn decl, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_generic_fn() {
        let source = r#"fn identity<T>(x: T): T = x"#;
        let module = parse_module(source, "test").expect("should parse");
        match &module.decls[0] {
            Decl::Fn { name, type_params, params, ret_ty, .. } => {
                assert_eq!(name.as_str(), "identity");
                assert_eq!(type_params.len(), 1);
                assert_eq!(type_params[0].as_str(), "T");
                assert_eq!(params.len(), 1);
                assert!(matches!(&params[0].1, Ty::Var(v) if v == "T"));
                assert!(matches!(ret_ty, Ty::Var(v) if v == "T"));
            }
            other => panic!("Expected Fn decl, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_multi_type_params() {
        let source = r#"fn swap<A, B>(x: A, y: B): B = y"#;
        let module = parse_module(source, "test").expect("should parse");
        match &module.decls[0] {
            Decl::Fn { type_params, .. } => {
                assert_eq!(type_params.len(), 2);
                assert_eq!(type_params[0].as_str(), "A");
                assert_eq!(type_params[1].as_str(), "B");
            }
            other => panic!("Expected Fn decl, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_pub_generic_fn() {
        let source = r#"pub fn identity<T>(x: T): T = x"#;
        let module = parse_module(source, "test").expect("should parse");
        match &module.decls[0] {
            Decl::Fn { visibility, type_params, .. } => {
                assert_eq!(*visibility, Visibility::Public);
                assert_eq!(type_params.len(), 1);
            }
            other => panic!("Expected Fn decl, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_import() {
        let source = r#"
            import utils
            fn main(): I32 = 42
        "#;
        let module = parse_module(source, "test").expect("should parse");
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].module.as_str(), "utils");
        assert!(module.imports[0].names.is_empty());
        assert_eq!(module.decls.len(), 1);
    }

    #[test]
    fn test_parse_import_specific_names() {
        let source = r#"
            import utils(double, triple)
            fn main(): I32 = double(21)
        "#;
        let module = parse_module(source, "test").expect("should parse");
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].module.as_str(), "utils");
        assert_eq!(module.imports[0].names.len(), 2);
        assert_eq!(module.imports[0].names[0].as_str(), "double");
        assert_eq!(module.imports[0].names[1].as_str(), "triple");
    }

    #[test]
    fn test_parse_pub_type() {
        let source = r#"pub type Alias = I32"#;
        let module = parse_module(source, "test").expect("should parse");
        match &module.decls[0] {
            Decl::Type { name, visibility, .. } => {
                assert_eq!(name.as_str(), "Alias");
                assert_eq!(*visibility, Visibility::Public);
            }
            other => panic!("Expected Type decl, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_perform() {
        let source = r#"perform print(42)"#;
        let expr = parse(source).expect("should parse");
        match &expr.kind {
            ExprKind::Perform { op, args } => {
                assert_eq!(op.as_str(), "print");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Perform, got {:?}", expr.kind),
        }
    }

    #[test]
    fn test_parse_perform_no_args() {
        let source = r#"perform yield"#;
        let expr = parse(source).expect("should parse");
        match &expr.kind {
            ExprKind::Perform { op, args } => {
                assert_eq!(op.as_str(), "yield");
                assert!(args.is_empty());
            }
            _ => panic!("Expected Perform, got {:?}", expr.kind),
        }
    }

    #[test]
    fn test_parse_handle() {
        let source = r#"handle 42 with return(x) => x end"#;
        let expr = parse(source).expect("should parse");
        match &expr.kind {
            ExprKind::Handle { clauses, .. } => {
                assert_eq!(clauses.len(), 1);
                assert!(clauses[0].op.is_empty()); // return clause
            }
            _ => panic!("Expected Handle, got {:?}", expr.kind),
        }
    }

    #[test]
    fn test_parse_handle_with_op() {
        let source = r#"handle perform ask() with
            | return(x) => x
            | ask(k) => k
        end"#;
        let result = parse(source);
        assert!(result.is_ok(), "should parse handle with op: {:?}", result.err());
        match result.unwrap().kind {
            ExprKind::Handle { clauses, .. } => {
                assert_eq!(clauses.len(), 2);
                assert!(clauses[0].op.is_empty()); // return
                assert_eq!(clauses[1].op.as_str(), "ask");
            }
            other => panic!("Expected Handle, got {other:?}"),
        }
    }
}
