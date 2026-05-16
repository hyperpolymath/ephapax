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
    BaseTy, BinOp, ConstructorDef, DataDecl, ExternBlock, ExternItem, Literal, MatchArm, Pattern,
    Span, SurfaceDecl, SurfaceExpr, SurfaceExprKind, SurfaceImport, SurfaceModule, SurfaceTy,
    SurfaceVisibility, UnaryOp,
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
    let mut imports = Vec::new();
    let mut module_name = SmolStr::new(name);

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::declaration => {
                decls.push(parse_surface_declaration(inner).map_err(|e| vec![e])?);
            }
            Rule::import_decl => {
                imports.push(parse_surface_import(inner).map_err(|e| vec![e])?);
            }
            Rule::module_decl => {
                // `module a/b/c` — the qualified_name is the only child.
                if let Some(qn) = inner.into_inner().next() {
                    module_name = SmolStr::new(qn.as_str());
                }
            }
            _ => {}
        }
    }

    Ok(SurfaceModule {
        name: module_name,
        imports,
        decls,
    })
}

fn parse_surface_import(
    pair: pest::iterators::Pair<Rule>,
) -> Result<SurfaceImport, ParseError> {
    let mut inner = pair.into_inner();
    let module_pair = inner
        .next()
        .ok_or_else(|| ParseError::missing("import module path"))?;
    let module = SmolStr::new(module_pair.as_str());

    let mut names = Vec::new();
    for item in inner {
        if item.as_rule() == Rule::identifier {
            names.push(SmolStr::new(item.as_str()));
        }
    }
    Ok(SurfaceImport { module, names })
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

fn parse_surface_declaration(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    // A `declaration` is now `annotation* ~ (data_decl | fn_decl | type_decl
    // | extern_block | const_decl)`. Skip past any leading annotations to
    // find the actual decl pair. Annotation metadata is dropped at the
    // parser layer for now — see the `annotation` rule in ephapax.pest.
    let inner = pair
        .into_inner()
        .find(|p| p.as_rule() != Rule::annotation)
        .ok_or_else(|| ParseError::unexpected_end("declaration"))?;

    match inner.as_rule() {
        Rule::data_decl => parse_data_decl(inner),
        Rule::fn_decl => parse_fn_decl(inner),
        Rule::type_decl => parse_type_decl(inner),
        Rule::extern_block => parse_extern_block(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected declaration: {:?}", inner.as_rule()),
            span: span_from_pair(&inner),
        }),
    }
}

fn parse_extern_block(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    let mut inner = pair.into_inner();

    let abi_pair = inner
        .next()
        .ok_or_else(|| ParseError::missing("extern ABI string"))?;
    // The ABI token is a `string` (which is `"..."` quoted) — strip the
    // surrounding quotes.
    let abi_raw = abi_pair.as_str();
    let abi = SmolStr::new(abi_raw.trim_start_matches('"').trim_end_matches('"'));

    let mut items = Vec::new();
    for item in inner {
        if item.as_rule() == Rule::extern_item {
            items.push(parse_extern_item(item)?);
        }
    }

    Ok(SurfaceDecl::Extern(ExternBlock { abi, items }))
}

fn parse_extern_item(pair: pest::iterators::Pair<Rule>) -> Result<ExternItem, ParseError> {
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("extern item"))?;

    match inner.as_rule() {
        Rule::extern_type => {
            let name_pair = inner
                .into_inner()
                .next()
                .ok_or_else(|| ParseError::missing("extern type name"))?;
            Ok(ExternItem::Type(parse_identifier(name_pair)))
        }
        Rule::extern_fn => {
            let mut parts = inner.into_inner();
            let name = parse_identifier(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("extern fn name"))?,
            );

            let mut params = Vec::new();
            let mut ret_ty = None;

            for item in parts {
                match item.as_rule() {
                    Rule::param_list => {
                        for param in item.into_inner() {
                            if param.as_rule() == Rule::param {
                                let mut pp = param.into_inner();
                                let pname = parse_identifier(
                                    pp.next()
                                        .ok_or_else(|| ParseError::missing("extern param name"))?,
                                );
                                let pty = parse_type(
                                    pp.next()
                                        .ok_or_else(|| ParseError::missing("extern param type"))?,
                                )?;
                                params.push((pname, pty));
                            }
                        }
                    }
                    Rule::ty => {
                        if ret_ty.is_none() {
                            ret_ty = Some(parse_type(item)?);
                        }
                    }
                    _ => {}
                }
            }

            Ok(ExternItem::Fn {
                name,
                params,
                ret_ty: ret_ty.unwrap_or(SurfaceTy::Base(BaseTy::Unit)),
            })
        }
        other => Err(ParseError::Syntax {
            message: format!("Unexpected extern item: {:?}", other),
            span: Span::dummy(),
        }),
    }
}

fn parse_data_decl(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair.into_inner();

    // `visibility?` may precede the constructor name (e.g. `pub data
    // Department = ...`). Surface AST doesn't track data-decl visibility
    // explicitly today — but we still need to skip past the pair to find
    // the actual name. Data exports remain implicitly public for now.
    let mut name: Option<smol_str::SmolStr> = None;
    let mut params = Vec::new();
    let mut constructors = Vec::new();

    for item in inner {
        if name.is_none() && item.as_rule() == Rule::visibility {
            continue;
        }
        if name.is_none() && item.as_rule() == Rule::constructor_name {
            name = Some(parse_constructor_name(item));
            continue;
        }
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
        name: name.ok_or_else(|| ParseError::missing("data type name"))?,
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
    let inner = pair.into_inner();

    let mut visibility = SurfaceVisibility::Private;
    let mut name: Option<ephapax_surface::Var> = None;
    let mut params = Vec::new();
    let mut ret_ty = None;
    let mut body = None;

    for item in inner {
        match item.as_rule() {
            Rule::visibility => {
                visibility = SurfaceVisibility::Public;
            }
            Rule::identifier if name.is_none() => {
                name = Some(parse_identifier(item));
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

    Ok(SurfaceDecl::Fn {
        name: name.ok_or_else(|| ParseError::missing("function name"))?,
        visibility,
        params,
        ret_ty: ret_ty.unwrap_or(SurfaceTy::Base(BaseTy::Unit)),
        body: body.unwrap_or_else(|| SurfaceExpr::dummy(SurfaceExprKind::Lit(Literal::Unit))),
    })
}

fn parse_type_decl(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceDecl, ParseError> {
    let inner = pair.into_inner();

    let mut visibility = SurfaceVisibility::Private;
    let mut name: Option<ephapax_surface::Var> = None;
    let mut ty: Option<SurfaceTy> = None;

    for item in inner {
        match item.as_rule() {
            Rule::visibility => visibility = SurfaceVisibility::Public,
            Rule::identifier if name.is_none() => name = Some(parse_identifier(item)),
            Rule::ty if ty.is_none() => ty = Some(parse_type(item)?),
            // `type Foo = { f1: T1, f2: T2 }` — record type alias. Lower
            // to a right-nested binary product of field types (field
            // names are not preserved in the surface AST today; record
            // access happens via tuple `.0`/`.1` projections after
            // desugar). Bridge.eph relies on this for `type Model = {..}`.
            Rule::record_type_def if ty.is_none() => {
                let mut field_tys: Vec<SurfaceTy> = Vec::new();
                for fld in item.into_inner() {
                    if fld.as_rule() == Rule::record_field {
                        // record_field = identifier ~ ":" ~ ty
                        let mut parts = fld.into_inner();
                        let _name = parts.next();
                        if let Some(t) = parts.next() {
                            field_tys.push(parse_type(t)?);
                        }
                    }
                }
                ty = Some(field_tys_to_product(field_tys));
            }
            // `type Foo = | A | B(I32)` — sum type alias. Same approach,
            // lower to a binary sum of variant payloads.
            Rule::sum_type_def if ty.is_none() => {
                let mut variant_tys: Vec<SurfaceTy> = Vec::new();
                for v in item.into_inner() {
                    if v.as_rule() == Rule::sum_variant {
                        let mut parts = v.into_inner();
                        let _name = parts.next();
                        match parts.next() {
                            Some(t) => variant_tys.push(parse_type(t)?),
                            None => variant_tys.push(SurfaceTy::Base(BaseTy::Unit)),
                        }
                    }
                }
                ty = Some(field_tys_to_sum(variant_tys));
            }
            _ => {}
        }
    }

    Ok(SurfaceDecl::Type {
        name: name.ok_or_else(|| ParseError::missing("type name"))?,
        visibility,
        ty: ty.ok_or_else(|| ParseError::missing("type definition"))?,
    })
}

fn field_tys_to_product(tys: Vec<SurfaceTy>) -> SurfaceTy {
    match tys.len() {
        0 => SurfaceTy::Base(BaseTy::Unit),
        1 => tys.into_iter().next().expect("len == 1"),
        2 => {
            let mut iter = tys.into_iter();
            SurfaceTy::Prod {
                left: Box::new(iter.next().expect("len == 2")),
                right: Box::new(iter.next().expect("len == 2")),
            }
        }
        _ => SurfaceTy::Tuple(tys),
    }
}

fn field_tys_to_sum(tys: Vec<SurfaceTy>) -> SurfaceTy {
    let mut iter = tys.into_iter().rev();
    let mut acc = match iter.next() {
        Some(t) => t,
        None => return SurfaceTy::Base(BaseTy::Unit),
    };
    for t in iter {
        acc = SurfaceTy::Sum {
            left: Box::new(t),
            right: Box::new(acc),
        };
    }
    acc
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
        Rule::seq_expr => parse_seq_expr(inner),
        // Legacy: if expression directly contains a single_expr child
        Rule::single_expr => parse_single_expr(inner),
        Rule::block_expr => parse_block_expr(inner),
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

/// Parse a semicolon-separated sequence of expressions.
///
/// `e1 ; e2 ; e3` desugars to `let _ = e1 in let _ = e2 in e3`.
fn parse_seq_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let exprs: Vec<_> = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::single_expr)
        .collect();

    if exprs.is_empty() {
        return Ok(SurfaceExpr::new(SurfaceExprKind::Lit(Literal::Unit), span));
    }

    // Parse all sub-expressions
    let mut parsed: Vec<SurfaceExpr> = Vec::with_capacity(exprs.len());
    for e in exprs {
        parsed.push(parse_single_expr(e)?);
    }

    // If only one expression, return it directly (no sequencing)
    if parsed.len() == 1 {
        // invariant: len() == 1 guarantees next() returns Some
        return Ok(parsed.into_iter().next().expect("invariant: parsed.len() == 1"));
    }

    // Desugar e1 ; e2 ; ... ; eN into nested lets:
    //   let _ = e1 in (let _ = e2 in (... eN))
    // invariant: loop above ensures parsed is not empty before we enter this block
    let last = parsed.pop().expect("invariant: parsed is not empty");
    parsed.into_iter().rev().fold(Ok(last), |acc, expr| {
        let acc = acc?;
        let s = expr.span;
        Ok(SurfaceExpr::new(
            SurfaceExprKind::Let {
                name: SmolStr::new("_"),
                ty: None,
                value: Box::new(expr),
                body: Box::new(acc),
            },
            s,
        ))
    })
}

/// Parse a single (non-sequenced) expression.
fn parse_single_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("single expression"))?;

    match inner.as_rule() {
        Rule::block_expr => parse_block_expr(inner),
        Rule::let_expr => parse_let_expr(inner),
        Rule::let_lin_expr => parse_let_lin_expr(inner),
        Rule::lambda_expr => parse_lambda_expr(inner),
        Rule::if_expr => parse_if_expr(inner),
        Rule::region_expr => parse_region_expr(inner),
        Rule::match_expr => parse_match_expr(inner),
        Rule::case_expr => parse_case_expr(inner),
        Rule::or_expr => parse_or_expr(inner),
        _ => Err(ParseError::Syntax {
            message: format!("Unexpected single_expr rule: {:?}", inner.as_rule()),
            span,
        }),
    }
}

/// Parse an implicit-`in` block: a chain of `let`/`let!` bindings without
/// trailing `in` followed by a result expression. Folds into nested
/// `Let` / `LetLin` AST nodes.
fn parse_block_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let children: Vec<_> = pair.into_inner().collect();

    // Children: zero or more `sequential_let` pairs, then exactly one final
    // `expression`. The grammar guarantees `sequential_let+`, so we can
    // unwrap the trailing expression.
    let (lets, trailing): (Vec<_>, Vec<_>) = children
        .into_iter()
        .partition(|p| p.as_rule() == Rule::sequential_let);
    let trailing_expr = trailing
        .into_iter()
        .find(|p| p.as_rule() == Rule::expression)
        .ok_or_else(|| ParseError::missing("block trailing expression"))?;
    let mut body = parse_expression(trailing_expr)?;

    // Fold from the right: the last let wraps the trailing expression as
    // its body, the previous let wraps that, etc.
    for stmt in lets.into_iter().rev() {
        body = parse_sequential_let(stmt, body, span)?;
    }
    Ok(body)
}

/// Parse one `sequential_let` (a `let` / `let!` without trailing `in`)
/// against an already-parsed body expression. Reuses the tuple-binder
/// lowering from [`match_arm_from_tuple_binder`].
fn parse_sequential_let(
    pair: pest::iterators::Pair<Rule>,
    body: SurfaceExpr,
    span: Span,
) -> Result<SurfaceExpr, ParseError> {
    // The first token (`let` or `let!`) is consumed by the grammar but
    // doesn't appear as a Pair — we detect it from the source slice.
    let src = pair.as_str();
    let is_linear = src.trim_start().starts_with("let!");

    let mut inner = pair.into_inner();
    let binder = parse_let_binder(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("sequential let binder"))?,
    )?;

    let mut ty = None;
    let mut value = None;
    for item in inner {
        match item.as_rule() {
            Rule::ty if ty.is_none() => ty = Some(parse_type(item)?),
            Rule::block_rhs if value.is_none() => value = Some(parse_block_rhs(item)?),
            _ => {}
        }
    }
    let value = value.ok_or_else(|| ParseError::missing("sequential let value"))?;

    Ok(match (binder, is_linear) {
        (LetBinder::Single(name), false) => SurfaceExpr::new(
            SurfaceExprKind::Let {
                name,
                ty,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        ),
        (LetBinder::Single(name), true) => SurfaceExpr::new(
            SurfaceExprKind::LetLin {
                name,
                ty,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        ),
        (LetBinder::Tuple(names), _) => match_arm_from_tuple_binder(names, value, body, span),
    })
}

fn parse_block_rhs(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("block rhs"))?;
    match inner.as_rule() {
        Rule::lambda_expr => parse_lambda_expr(inner),
        Rule::if_expr => parse_if_expr(inner),
        Rule::region_expr => parse_region_expr(inner),
        Rule::match_expr => parse_match_expr(inner),
        Rule::case_expr => parse_case_expr(inner),
        Rule::or_expr => parse_or_expr(inner),
        other => Err(ParseError::Syntax {
            message: format!("Unexpected block rhs rule: {:?}", other),
            span,
        }),
    }
}

/// A parsed `let_binder` — either a single identifier or a list of
/// identifiers from a `tuple_binder`. Tuple binders are lowered to a
/// 1-arm match at the parse site.
enum LetBinder {
    Single(ephapax_surface::Var),
    Tuple(Vec<ephapax_surface::Var>),
}

fn parse_let_binder(pair: pest::iterators::Pair<Rule>) -> Result<LetBinder, ParseError> {
    // `let_binder = { tuple_binder | identifier }`
    let inner = pair
        .into_inner()
        .next()
        .ok_or_else(|| ParseError::unexpected_end("let binder"))?;
    match inner.as_rule() {
        Rule::identifier => Ok(LetBinder::Single(parse_identifier(inner))),
        Rule::tuple_binder => {
            let names: Vec<_> = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::identifier)
                .map(parse_identifier)
                .collect();
            if names.len() < 2 {
                return Err(ParseError::Syntax {
                    message: "tuple binder must have at least 2 names".into(),
                    span: Span::dummy(),
                });
            }
            Ok(LetBinder::Tuple(names))
        }
        other => Err(ParseError::Syntax {
            message: format!("Unexpected let binder: {:?}", other),
            span: Span::dummy(),
        }),
    }
}

/// Build a 1-arm `match scrutinee of | (a, b, ...) => body end` from a
/// tuple-binder lowering. For N=2 the pattern is `Pattern::Pair`; for N>2
/// it becomes a right-nested chain of `Pattern::Pair`s to match ephapax's
/// existing binary-product encoding.
fn match_arm_from_tuple_binder(
    binders: Vec<ephapax_surface::Var>,
    scrutinee: SurfaceExpr,
    body: SurfaceExpr,
    span: Span,
) -> SurfaceExpr {
    // Build the pair pattern from the right: (a, b, c) → Pair(a, Pair(b, c)).
    let mut iter = binders.into_iter().rev();
    let last = iter.next().expect("at least 2 binders");
    let mut pat = Pattern::Var(last);
    for name in iter {
        pat = Pattern::Pair(Box::new(Pattern::Var(name)), Box::new(pat));
    }
    SurfaceExpr::new(
        SurfaceExprKind::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![MatchArm {
                pattern: pat,
                guard: None,
                body,
            }],
        },
        span,
    )
}

fn parse_let_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let binder = parse_let_binder(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("let binder"))?,
    )?;

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

    let value = value.ok_or_else(|| ParseError::missing("let value"))?;
    let body = body.ok_or_else(|| ParseError::missing("let body"))?;

    match binder {
        LetBinder::Single(name) => Ok(SurfaceExpr::new(
            SurfaceExprKind::Let {
                name,
                ty,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        )),
        LetBinder::Tuple(names) => Ok(match_arm_from_tuple_binder(names, value, body, span)),
    }
}

fn parse_let_lin_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let binder = parse_let_binder(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("let! binder"))?,
    )?;

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

    let value = value.ok_or_else(|| ParseError::missing("let! value"))?;
    let body = body.ok_or_else(|| ParseError::missing("let! body"))?;

    match binder {
        LetBinder::Single(name) => Ok(SurfaceExpr::new(
            SurfaceExprKind::LetLin {
                name,
                ty,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        )),
        LetBinder::Tuple(names) => Ok(match_arm_from_tuple_binder(names, value, body, span)),
    }
}

fn parse_lambda_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let param = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("param"))?);
    let param_ty = parse_type(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("param type"))?,
    )?;
    let body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("lambda body"))?,
    )?;

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

    let scrutinee = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("case scrutinee"))?,
    )?;
    let left_var = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("inl var"))?);
    let left_body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("inl body"))?,
    )?;
    let right_var = parse_identifier(inner.next().ok_or_else(|| ParseError::missing("inr var"))?);
    let right_body = parse_expression(
        inner
            .next()
            .ok_or_else(|| ParseError::missing("inr body"))?,
    )?;

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
    let mut exprs: Vec<pest::iterators::Pair<Rule>> =
        inner.filter(|p| p.as_rule() == Rule::expression).collect();

    let (guard, body) = if exprs.len() >= 2 {
        // invariant: len() >= 2 guarantees pop() returns Some twice
        let body = parse_expression(exprs.pop().expect("invariant: exprs.len() >= 2"))?;
        let guard_expr = parse_expression(exprs.pop().expect("invariant: exprs.len() >= 2"))?;
        (Some(Box::new(guard_expr)), body)
    } else if exprs.len() == 1 {
        // invariant: len() == 1 guarantees pop() returns Some
        (None, parse_expression(exprs.pop().expect("invariant: exprs.len() == 1"))?)
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
            let left = parse_pattern(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("left pattern"))?,
            )?;
            let right = parse_pattern(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("right pattern"))?,
            )?;
            Ok(Pattern::Pair(Box::new(left), Box::new(right)))
        }
        Rule::wildcard_pattern => Ok(Pattern::Wildcard),
        Rule::literal_pattern => {
            let lit_pair = inner
                .into_inner()
                .next()
                .ok_or_else(|| ParseError::missing("literal"))?;
            let lit = parse_literal_value(lit_pair)?;
            Ok(Pattern::Literal(lit))
        }
        Rule::var_pattern => {
            let name = parse_identifier(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("var pattern"))?,
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
    let mut left = parse_and_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("or_expr"))?,
    )?;

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
    let mut left = parse_eq_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("and_expr"))?,
    )?;

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
    let mut left = parse_cmp_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("eq_expr"))?,
    )?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "==" => BinOp::Eq,
            "!=" => BinOp::Ne,
            _ => {
                return Err(ParseError::Syntax {
                    message: format!("Unknown eq op: {}", op_pair.as_str()),
                    span: span_from_pair(&op_pair),
                })
            }
        };
        let right = parse_cmp_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(left)
}

fn parse_cmp_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_add_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("cmp_expr"))?,
    )?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "<" => BinOp::Lt,
            "<=" => BinOp::Le,
            ">" => BinOp::Gt,
            ">=" => BinOp::Ge,
            _ => {
                return Err(ParseError::Syntax {
                    message: format!("Unknown cmp op: {}", op_pair.as_str()),
                    span: span_from_pair(&op_pair),
                })
            }
        };
        let right = parse_add_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(left)
}

fn parse_add_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_mul_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("add_expr"))?,
    )?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            _ => {
                return Err(ParseError::Syntax {
                    message: format!("Unknown add op: {}", op_pair.as_str()),
                    span: span_from_pair(&op_pair),
                })
            }
        };
        let right = parse_mul_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
            span,
        );
    }
    Ok(left)
}

fn parse_mul_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = parse_unary_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("mul_expr"))?,
    )?;

    while let Some(op_pair) = inner.next() {
        let op = match op_pair.as_str() {
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,
            _ => {
                return Err(ParseError::Syntax {
                    message: format!("Unknown mul op: {}", op_pair.as_str()),
                    span: span_from_pair(&op_pair),
                })
            }
        };
        let right = parse_unary_expr(inner.next().ok_or_else(|| ParseError::missing("rhs"))?)?;
        left = SurfaceExpr::new(
            SurfaceExprKind::BinOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
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
                let operand =
                    parse_unary_expr(inner.next().ok_or_else(|| ParseError::missing("operand"))?)?;
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
                let operand =
                    parse_unary_expr(inner.next().ok_or_else(|| ParseError::missing("operand"))?)?;
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
    let next = inner
        .next()
        .ok_or_else(|| ParseError::unexpected_end("unary"))?;
    parse_postfix_expr(next)
}

fn parse_postfix_expr(pair: pest::iterators::Pair<Rule>) -> Result<SurfaceExpr, ParseError> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let base = parse_atom_expr(
        inner
            .next()
            .ok_or_else(|| ParseError::unexpected_end("postfix"))?,
    )?;

    let mut result = base;
    for op in inner {
        if op.as_rule() == Rule::postfix_op {
            let op_inner = op
                .into_inner()
                .next()
                .ok_or_else(|| ParseError::unexpected_end("postfix op"))?;
            match op_inner.as_rule() {
                Rule::call_op => {
                    let call_inner: Vec<_> = op_inner.into_inner().collect();
                    if call_inner.is_empty() {
                        // Zero-arg call: foo() → App(foo, ())
                        result = SurfaceExpr::new(
                            SurfaceExprKind::App {
                                func: Box::new(result),
                                arg: Box::new(SurfaceExpr::new(
                                    SurfaceExprKind::Lit(Literal::Unit),
                                    span,
                                )),
                            },
                            span,
                        );
                    } else {
                        // call_args: one or more comma-separated expressions
                        // Parse all args from the call_args rule
                        let args_pair = &call_inner[0];
                        let arg_exprs: Vec<_> = args_pair
                            .clone()
                            .into_inner()
                            .filter(|p| p.as_rule() == Rule::expression)
                            .collect();
                        // Curry: f(a, b, c) → App(App(App(f, a), b), c)
                        for arg_pair in arg_exprs {
                            let arg = parse_expression(arg_pair)?;
                            result = SurfaceExpr::new(
                                SurfaceExprKind::App {
                                    func: Box::new(result),
                                    arg: Box::new(arg),
                                },
                                span,
                            );
                        }
                    }
                }
                Rule::index_op => {
                    let idx_pair = op_inner
                        .into_inner()
                        .next()
                        .ok_or_else(|| ParseError::missing("index"))?;
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
                    let member = op_inner
                        .into_inner()
                        .next()
                        .ok_or_else(|| ParseError::missing("member"))?;
                    match member.as_rule() {
                        Rule::integer => {
                            let idx: usize =
                                member.as_str().parse().map_err(|_| ParseError::Syntax {
                                    message: "Invalid tuple index".into(),
                                    span: span_from_pair(&member),
                                })?;
                            if idx == 0 {
                                result =
                                    SurfaceExpr::new(SurfaceExprKind::Fst(Box::new(result)), span);
                            } else if idx == 1 {
                                result =
                                    SurfaceExpr::new(SurfaceExprKind::Snd(Box::new(result)), span);
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
            let symbol_pair = parts
                .next()
                .ok_or_else(|| ParseError::missing("ffi symbol"))?;
            let symbol = parse_string_value(symbol_pair);
            let mut args = Vec::new();
            for p in parts {
                if p.as_rule() == Rule::expression {
                    args.push(parse_expression(p)?);
                }
            }
            Ok(SurfaceExpr::new(
                SurfaceExprKind::FFI { symbol, args },
                span,
            ))
        }

        Rule::string_method => {
            let mut parts = inner.into_inner();
            let method =
                parse_identifier(parts.next().ok_or_else(|| ParseError::missing("method"))?);

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
                    Ok(SurfaceExpr::new(
                        SurfaceExprKind::StringNew { region, value },
                        span,
                    ))
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
                        SurfaceExprKind::StringLen(Box::new(arg.unwrap_or_else(|| {
                            SurfaceExpr::dummy(SurfaceExprKind::Lit(Literal::Unit))
                        }))),
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
            Ok(SurfaceExpr::new(
                SurfaceExprKind::Inl {
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
            Ok(SurfaceExpr::new(
                SurfaceExprKind::Inr {
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
                    .ok_or_else(|| ParseError::missing("borrow"))?,
            )?;
            Ok(SurfaceExpr::new(
                SurfaceExprKind::Borrow(Box::new(inner_expr)),
                span,
            ))
        }

        Rule::drop_expr => {
            let inner_expr = parse_expression(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("drop"))?,
            )?;
            Ok(SurfaceExpr::new(
                SurfaceExprKind::Drop(Box::new(inner_expr)),
                span,
            ))
        }

        Rule::copy_expr => {
            let inner_expr = parse_expression(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("copy"))?,
            )?;
            Ok(SurfaceExpr::new(
                SurfaceExprKind::Copy(Box::new(inner_expr)),
                span,
            ))
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

        // Record literal `{ f1 = v1, f2 = v2 }` (or `f: v` / `f: ty = v`
        // shorthands). Field names aren't preserved in the surface AST
        // today — lower to a positional product (`Pair`/`TupleLit`)
        // matching the lowering used by `type Foo = { f1: T1, f2: T2 }`
        // in `parse_type_decl`. Bridge.eph + hypatia_gui.eph rely on this.
        Rule::record_literal => {
            let mut values = Vec::new();
            for fld in inner.into_inner() {
                if fld.as_rule() == Rule::record_field_assign {
                    let mut value: Option<SurfaceExpr> = None;
                    for part in fld.into_inner() {
                        match part.as_rule() {
                            Rule::expression => value = Some(parse_expression(part)?),
                            _ => {}
                        }
                    }
                    if let Some(v) = value {
                        values.push(v);
                    }
                }
            }
            Ok(match values.len() {
                0 => SurfaceExpr::new(SurfaceExprKind::Lit(Literal::Unit), span),
                1 => values.into_iter().next().expect("len == 1"),
                2 => {
                    let mut iter = values.into_iter();
                    let left = iter.next().expect("len == 2");
                    let right = iter.next().expect("len == 2");
                    SurfaceExpr::new(
                        SurfaceExprKind::Pair {
                            left: Box::new(left),
                            right: Box::new(right),
                        },
                        span,
                    )
                }
                _ => SurfaceExpr::new(SurfaceExprKind::TupleLit(values), span),
            })
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
                1 => {
                    // invariant: match arm 1 guarantees len() == 1, so next() returns Some
                    Ok(exprs.into_iter().next().expect("invariant: exprs.len() == 1"))
                }
                2 => {
                    let mut iter = exprs.into_iter();
                    // invariant: match arm 2 guarantees len() == 2, so next() returns Some twice
                    let left = iter.next().expect("invariant: exprs.len() == 2");
                    let right = iter.next().expect("invariant: exprs.len() == 2");
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
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("variable name"))?,
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
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("borrow inner"))?,
            )?;
            Ok(SurfaceTy::Borrow(Box::new(inner_ty)))
        }
        Rule::list_ty => {
            let elem_ty = parse_type(
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("list element type"))?,
            )?;
            Ok(SurfaceTy::List(Box::new(elem_ty)))
        }
        Rule::product_ty => {
            let mut tys: Vec<SurfaceTy> = inner
                .into_inner()
                .filter(|p| p.as_rule() == Rule::ty)
                .map(parse_type)
                .collect::<Result<_, _>>()?;
            // Match the value-side convention in `paren_or_pair`: exactly two
            // elements form a binary product (`Prod`, matched by `fst`/`snd`
            // and `Pattern::Pair`); three or more elements form a TupleLit /
            // SurfaceTy::Tuple. This keeps `(I32, I32)` as a type compatible
            // with `(1, 2)` as a value.
            if tys.len() == 2 {
                let right = tys.remove(1);
                let left = tys.remove(0);
                Ok(SurfaceTy::Prod {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            } else {
                Ok(SurfaceTy::Tuple(tys))
            }
        }
        Rule::named_ty => {
            let mut parts = inner.into_inner();
            let name = parse_constructor_name(
                parts
                    .next()
                    .ok_or_else(|| ParseError::missing("type name"))?,
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
                inner
                    .into_inner()
                    .next()
                    .ok_or_else(|| ParseError::missing("type var"))?,
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
    // base_ty = { unit_ty | "Bool" | "I32" | "I64" | "F32" | "F64" }
    // Literal string matches ("Bool", "I32", etc.) don't have inner children
    // in pest, so we check the pair's text directly.
    let text = pair.as_str().trim();

    match text {
        "()" => Ok(SurfaceTy::Base(BaseTy::Unit)),
        "Bool" => Ok(SurfaceTy::Base(BaseTy::Bool)),
        "I32" => Ok(SurfaceTy::Base(BaseTy::I32)),
        "I64" => Ok(SurfaceTy::Base(BaseTy::I64)),
        "F32" => Ok(SurfaceTy::Base(BaseTy::F32)),
        "F64" => Ok(SurfaceTy::Base(BaseTy::F64)),
        _ => {
            // Fallback: treat unknown type text as Unit
            // (covers unit_ty rule and any unrecognised fragments)
            let _ = pair.into_inner(); // consume inner pairs
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

    /// Slash-separated module paths (the `hypatia/ui/bridge` shape used by
    /// downstream consumers) must parse alongside the historical dot form.
    #[test]
    fn parse_module_with_slash_path() {
        let source = "module hypatia/ui/bridge\n\nfn one(): I32 = 1";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.name.as_str(), "hypatia/ui/bridge");
        assert_eq!(module.decls.len(), 1);
    }

    /// Dot-separated module paths continue to work — the new rule admits
    /// both segment separators and the surface walker preserves whichever
    /// the file used.
    #[test]
    fn parse_module_with_dot_path() {
        let source = "module Foo.Bar.Baz\n\nfn two(): I32 = 2";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.name.as_str(), "Foo.Bar.Baz");
        assert_eq!(module.decls.len(), 1);
    }

    /// When the source has no `module` decl the surface walker falls back
    /// to the filename passed in, matching the pre-refactor behaviour.
    #[test]
    fn parse_module_without_decl_uses_filename() {
        let source = "fn three(): I32 = 3";
        let module = parse_surface_module(source, "fallback-name").unwrap();
        assert_eq!(module.name.as_str(), "fallback-name");
        assert_eq!(module.decls.len(), 1);
    }

    /// Bare `import` populates the surface module's imports vector.
    #[test]
    fn parse_surface_module_with_bare_import() {
        let source = "import utils\n\nfn one(): I32 = 1";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].module.as_str(), "utils");
        assert!(module.imports[0].names.is_empty());
        assert_eq!(module.decls.len(), 1);
    }

    /// Bare `import` with a slash-separated qualified path.
    #[test]
    fn parse_surface_module_with_slash_path_import() {
        let source = "import hypatia/ui/bridge\n\nfn one(): I32 = 1";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].module.as_str(), "hypatia/ui/bridge");
        assert!(module.imports[0].names.is_empty());
    }

    /// Selective `import M (a, b)` records each name.
    #[test]
    fn parse_surface_module_with_selective_import() {
        let source = "import utils (foo, bar)\n\nfn one(): I32 = 1";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0].module.as_str(), "utils");
        assert_eq!(module.imports[0].names.len(), 2);
        assert_eq!(module.imports[0].names[0].as_str(), "foo");
        assert_eq!(module.imports[0].names[1].as_str(), "bar");
    }

    /// Multiple `import` declarations all land in order.
    #[test]
    fn parse_surface_module_with_multiple_imports() {
        let source = "import a\nimport b/c (x)\n\nfn one(): I32 = 1";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.imports.len(), 2);
        assert_eq!(module.imports[0].module.as_str(), "a");
        assert_eq!(module.imports[1].module.as_str(), "b/c");
        assert_eq!(module.imports[1].names, vec![SmolStr::new("x")]);
    }

    /// Empty extern block — must parse, must carry the ABI tag, no items.
    #[test]
    fn parse_empty_extern_block() {
        let source = "extern \"gossamer\" { }\n";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.decls.len(), 1);
        match &module.decls[0] {
            SurfaceDecl::Extern { abi, items, .. } => {
                assert_eq!(abi, "gossamer");
                assert!(items.is_empty(), "no items expected");
            }
            other => panic!("expected SurfaceDecl::Extern, got {other:?}"),
        }
    }

    /// Extern block with type + fn items — the canonical hypatia
    /// `bridge.eph` shape. Asserts both item kinds round-trip into
    /// the surface AST.
    #[test]
    fn parse_extern_block_with_type_and_fn_items() {
        let source = "extern \"gossamer\" {
            type Window
            fn window_open(title: String, body: String): Window
        }";
        let module = parse_surface_module(source, "<input>").unwrap();
        match &module.decls[0] {
            SurfaceDecl::Extern { abi, items, .. } => {
                assert_eq!(abi, "gossamer");
                assert_eq!(items.len(), 2);
                match &items[0] {
                    SurfaceExternItem::Type { name } => {
                        assert_eq!(name.as_str(), "Window");
                    }
                    other => panic!("expected Type item, got {other:?}"),
                }
                match &items[1] {
                    SurfaceExternItem::Fn { name, params, .. } => {
                        assert_eq!(name.as_str(), "window_open");
                        assert_eq!(params.len(), 2);
                        assert_eq!(params[0].0.as_str(), "title");
                        assert_eq!(params[1].0.as_str(), "body");
                    }
                    other => panic!("expected Fn item, got {other:?}"),
                }
            }
            other => panic!("expected SurfaceDecl::Extern, got {other:?}"),
        }
    }

    /// Full module shape: slash-pathed module + import + extern block
    /// + regular fn declaration. Covers the bridge.eph prelude.
    #[test]
    fn parse_bridge_eph_shaped_prelude() {
        let source = "module hypatia/ui/bridge

extern \"gossamer\" {
    type Window
    fn window_open(title: String, body: String): Window
    fn window_close(w: Window): ()
}

fn entry(): I32 = 0";
        let module = parse_surface_module(source, "<input>").unwrap();
        assert_eq!(module.name.as_str(), "hypatia/ui/bridge");
        assert_eq!(module.decls.len(), 2, "extern block + fn decl");
        assert!(matches!(&module.decls[0], SurfaceDecl::Extern { .. }));
        assert!(matches!(&module.decls[1], SurfaceDecl::Fn { .. }));
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

    #[test]
    fn parse_and_desugar_eph_file() {
        let source = r#"
data Option(a) = None | Some(a)

fn test(opt: Option(I32)): I32 =
    match opt of
    | None => 0
    | Some(v) => v
    end
"#;
        let surface = parse_surface_module(source, "test").unwrap();
        assert_eq!(surface.decls.len(), 2);

        let core = ephapax_desugar::desugar(&surface).unwrap();
        assert_eq!(core.decls.len(), 1); // data consumed, only fn remains

        let result = ephapax_typing::type_check_module(&core);
        assert!(result.is_ok(), "type check failed: {:?}", result.err());
    }
}
