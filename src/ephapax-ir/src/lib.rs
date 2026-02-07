// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Ephapax S-expression IR bridge.
//!
//! Provides a small, stable S-expression encoding for Ephapax AST nodes.

use ephapax_syntax::{BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module, Ty, UnaryOp};
use smol_str::SmolStr;
use std::fmt;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

#[derive(Error, Debug, Clone, PartialEq)]
pub enum SExprError {
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("unexpected token: {0}")]
    UnexpectedToken(String),
    #[error("invalid S-expression: {0}")]
    Invalid(String),
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Atom(s) => write!(f, "{}", s),
            SExpr::List(items) => {
                write!(f, "(")?;
                for (idx, item) in items.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
        }
    }
}

pub fn parse_sexpr(input: &str) -> Result<SExpr, SExprError> {
    let mut chars = input.chars().peekable();
    let expr = parse_expr(&mut chars)?;
    consume_ws(&mut chars);
    if chars.peek().is_some() {
        return Err(SExprError::UnexpectedToken(
            chars.collect::<String>(),
        ));
    }
    Ok(expr)
}

fn parse_expr<I>(chars: &mut std::iter::Peekable<I>) -> Result<SExpr, SExprError>
where
    I: Iterator<Item = char>,
{
    consume_ws(chars);
    match chars.peek() {
        Some('(') => parse_list(chars),
        Some('"') => parse_string(chars).map(SExpr::Atom),
        Some(_) => parse_atom(chars).map(SExpr::Atom),
        None => Err(SExprError::UnexpectedEof),
    }
}

fn parse_list<I>(chars: &mut std::iter::Peekable<I>) -> Result<SExpr, SExprError>
where
    I: Iterator<Item = char>,
{
    match chars.next() {
        Some('(') => {}
        _ => return Err(SExprError::Invalid("expected '('".into())),
    }

    let mut items = Vec::new();
    loop {
        consume_ws(chars);
        match chars.peek() {
            Some(')') => {
                chars.next();
                break;
            }
            Some(_) => items.push(parse_expr(chars)?),
            None => return Err(SExprError::UnexpectedEof),
        }
    }
    Ok(SExpr::List(items))
}

fn parse_string<I>(chars: &mut std::iter::Peekable<I>) -> Result<String, SExprError>
where
    I: Iterator<Item = char>,
{
    match chars.next() {
        Some('"') => {}
        _ => return Err(SExprError::Invalid("expected '\"'".into())),
    }

    let mut out = String::new();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Ok(format!("\"{}\"", out)),
            '\\' => {
                let escaped = chars.next().ok_or(SExprError::UnexpectedEof)?;
                out.push(match escaped {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '"' => '"',
                    other => other,
                });
            }
            _ => out.push(c),
        }
    }
    Err(SExprError::UnexpectedEof)
}

fn parse_atom<I>(chars: &mut std::iter::Peekable<I>) -> Result<String, SExprError>
where
    I: Iterator<Item = char>,
{
    let mut out = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() || c == '(' || c == ')' {
            break;
        }
        out.push(c);
        chars.next();
    }
    if out.is_empty() {
        Err(SExprError::Invalid("empty atom".into()))
    } else {
        Ok(out)
    }
}

fn consume_ws<I>(chars: &mut std::iter::Peekable<I>)
where
    I: Iterator<Item = char>,
{
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}

pub fn module_to_sexpr(module: &Module) -> String {
    SExpr::List(vec![
        SExpr::Atom("module".into()),
        SExpr::Atom(escape_atom(&module.name)),
        SExpr::List(module.decls.iter().map(decl_to_sexpr).collect()),
    ])
    .to_string()
}

pub fn module_from_sexpr(sexpr: &str) -> Result<Module, SExprError> {
    let parsed = parse_sexpr(sexpr)?;
    match parsed {
        SExpr::List(items) => decode_module(&items),
        _ => Err(SExprError::Invalid("expected (module ...)".into())),
    }
}

fn decode_module(items: &[SExpr]) -> Result<Module, SExprError> {
    if items.len() != 3 {
        return Err(SExprError::Invalid("module requires name and decl list".into()));
    }
    if !is_atom(&items[0], "module") {
        return Err(SExprError::Invalid("expected 'module' tag".into()));
    }
    let name = atom_string(&items[1])?;
    let decls = match &items[2] {
        SExpr::List(ds) => ds.iter().map(decode_decl).collect::<Result<Vec<_>, _>>()?,
        _ => return Err(SExprError::Invalid("expected decl list".into())),
    };

    Ok(Module {
        name: SmolStr::new(name),
        decls,
    })
}

fn decl_to_sexpr(decl: &Decl) -> SExpr {
    match decl {
        Decl::Fn {
            name,
            params,
            ret_ty,
            body,
        } => SExpr::List(vec![
            SExpr::Atom("fn".into()),
            SExpr::Atom(escape_atom(name)),
            SExpr::List(
                params
                    .iter()
                    .map(|(p, t)| SExpr::List(vec![SExpr::Atom(escape_atom(p)), ty_to_sexpr(t)]))
                    .collect(),
            ),
            ty_to_sexpr(ret_ty),
            expr_to_sexpr(body),
        ]),
        Decl::Type { name, ty } => SExpr::List(vec![
            SExpr::Atom("type".into()),
            SExpr::Atom(escape_atom(name)),
            ty_to_sexpr(ty),
        ]),
    }
}

fn decode_decl(expr: &SExpr) -> Result<Decl, SExprError> {
    let list = match expr {
        SExpr::List(items) => items,
        _ => return Err(SExprError::Invalid("expected decl list".into())),
    };
    if list.is_empty() {
        return Err(SExprError::Invalid("empty decl".into()));
    }
    if is_atom(&list[0], "fn") {
        if list.len() != 5 {
            return Err(SExprError::Invalid("fn decl shape: (fn name (params) ret body)".into()));
        }
        let name = atom_string(&list[1])?;
        let params = match &list[2] {
            SExpr::List(items) => items
                .iter()
                .map(|p| match p {
                    SExpr::List(parts) if parts.len() == 2 => {
                        Ok((SmolStr::new(atom_string(&parts[0])?), decode_ty(&parts[1])?))
                    }
                    _ => Err(SExprError::Invalid("param must be (name ty)".into())),
                })
                .collect::<Result<Vec<_>, _>>()?,
            _ => return Err(SExprError::Invalid("params must be list".into())),
        };
        let ret_ty = decode_ty(&list[3])?;
        let body = decode_expr(&list[4])?;
        Ok(Decl::Fn {
            name: SmolStr::new(name),
            params,
            ret_ty,
            body,
        })
    } else if is_atom(&list[0], "type") {
        if list.len() != 3 {
            return Err(SExprError::Invalid("type decl shape: (type name ty)".into()));
        }
        let name = atom_string(&list[1])?;
        let ty = decode_ty(&list[2])?;
        Ok(Decl::Type {
            name: SmolStr::new(name),
            ty,
        })
    } else {
        Err(SExprError::Invalid("unknown decl".into()))
    }
}

fn expr_to_sexpr(expr: &Expr) -> SExpr {
    match &expr.kind {
        ExprKind::Lit(lit) => SExpr::List(vec![SExpr::Atom("lit".into()), lit_to_sexpr(lit)]),
        ExprKind::Var(name) => SExpr::List(vec![SExpr::Atom("var".into()), SExpr::Atom(escape_atom(name))]),
        ExprKind::StringNew { region, value } => SExpr::List(vec![
            SExpr::Atom("string-new".into()),
            SExpr::Atom(escape_atom(region)),
            SExpr::Atom(escape_string(value)),
        ]),
        ExprKind::StringConcat { left, right } => SExpr::List(vec![
            SExpr::Atom("string-concat".into()),
            expr_to_sexpr(left),
            expr_to_sexpr(right),
        ]),
        ExprKind::StringLen(inner) => SExpr::List(vec![SExpr::Atom("string-len".into()), expr_to_sexpr(inner)]),
        ExprKind::Let { name, value, body, .. } => SExpr::List(vec![
            SExpr::Atom("let".into()),
            SExpr::Atom(escape_atom(name)),
            expr_to_sexpr(value),
            expr_to_sexpr(body),
        ]),
        ExprKind::LetLin { name, value, body, .. } => SExpr::List(vec![
            SExpr::Atom("letlin".into()),
            SExpr::Atom(escape_atom(name)),
            expr_to_sexpr(value),
            expr_to_sexpr(body),
        ]),
        ExprKind::Lambda { param, param_ty, body } => SExpr::List(vec![
            SExpr::Atom("lambda".into()),
            SExpr::Atom(escape_atom(param)),
            ty_to_sexpr(param_ty),
            expr_to_sexpr(body),
        ]),
        ExprKind::App { func, arg } => SExpr::List(vec![
            SExpr::Atom("app".into()),
            expr_to_sexpr(func),
            expr_to_sexpr(arg),
        ]),
        ExprKind::Pair { left, right } => SExpr::List(vec![
            SExpr::Atom("pair".into()),
            expr_to_sexpr(left),
            expr_to_sexpr(right),
        ]),
        ExprKind::Fst(inner) => SExpr::List(vec![SExpr::Atom("fst".into()), expr_to_sexpr(inner)]),
        ExprKind::Snd(inner) => SExpr::List(vec![SExpr::Atom("snd".into()), expr_to_sexpr(inner)]),
        ExprKind::Inl { ty, value } => SExpr::List(vec![
            SExpr::Atom("inl".into()),
            ty_to_sexpr(ty),
            expr_to_sexpr(value),
        ]),
        ExprKind::Inr { ty, value } => SExpr::List(vec![
            SExpr::Atom("inr".into()),
            ty_to_sexpr(ty),
            expr_to_sexpr(value),
        ]),
        ExprKind::Case { scrutinee, left_var, left_body, right_var, right_body } => SExpr::List(vec![
            SExpr::Atom("case".into()),
            expr_to_sexpr(scrutinee),
            SExpr::List(vec![SExpr::Atom(escape_atom(left_var)), expr_to_sexpr(left_body)]),
            SExpr::List(vec![SExpr::Atom(escape_atom(right_var)), expr_to_sexpr(right_body)]),
        ]),
        ExprKind::If { cond, then_branch, else_branch } => SExpr::List(vec![
            SExpr::Atom("if".into()),
            expr_to_sexpr(cond),
            expr_to_sexpr(then_branch),
            expr_to_sexpr(else_branch),
        ]),
        ExprKind::Region { name, body } => SExpr::List(vec![
            SExpr::Atom("region".into()),
            SExpr::Atom(escape_atom(name)),
            expr_to_sexpr(body),
        ]),
        ExprKind::Borrow(inner) => SExpr::List(vec![SExpr::Atom("borrow".into()), expr_to_sexpr(inner)]),
        ExprKind::Deref(inner) => SExpr::List(vec![SExpr::Atom("deref".into()), expr_to_sexpr(inner)]),
        ExprKind::Drop(inner) => SExpr::List(vec![SExpr::Atom("drop".into()), expr_to_sexpr(inner)]),
        ExprKind::Copy(inner) => SExpr::List(vec![SExpr::Atom("copy".into()), expr_to_sexpr(inner)]),
        ExprKind::Block(exprs) => SExpr::List({
            let mut items = vec![SExpr::Atom("block".into())];
            items.extend(exprs.iter().map(expr_to_sexpr));
            items
        }),
        ExprKind::BinOp { op, left, right } => SExpr::List(vec![
            SExpr::Atom("binop".into()),
            SExpr::Atom(binop_to_atom(*op)),
            expr_to_sexpr(left),
            expr_to_sexpr(right),
        ]),
        ExprKind::UnaryOp { op, operand } => SExpr::List(vec![
            SExpr::Atom("unop".into()),
            SExpr::Atom(unary_to_atom(*op)),
            expr_to_sexpr(operand),
        ]),
        ExprKind::ListLit(elements) => {
            let mut elems = vec![SExpr::Atom("list-lit".into())];
            elems.extend(elements.iter().map(expr_to_sexpr));
            SExpr::List(elems)
        }
        ExprKind::ListIndex { list, index } => SExpr::List(vec![
            SExpr::Atom("list-index".into()),
            expr_to_sexpr(list),
            expr_to_sexpr(index),
        ]),
        ExprKind::TupleLit(elements) => {
            let mut elems = vec![SExpr::Atom("tuple-lit".into())];
            elems.extend(elements.iter().map(expr_to_sexpr));
            SExpr::List(elems)
        }
        ExprKind::TupleIndex { tuple, index } => SExpr::List(vec![
            SExpr::Atom("tuple-index".into()),
            expr_to_sexpr(tuple),
            SExpr::Atom(index.to_string()),
        ]),
    }
}

fn decode_expr(expr: &SExpr) -> Result<Expr, SExprError> {
    let list = match expr {
        SExpr::List(items) => items,
        _ => return Err(SExprError::Invalid("expected expr list".into())),
    };
    if list.is_empty() {
        return Err(SExprError::Invalid("empty expr".into()));
    }
    let tag = atom_string(&list[0])?;
    let kind = match tag.as_str() {
        "lit" => {
            if list.len() != 2 {
                return Err(SExprError::Invalid("(lit ...)".into()));
            }
            ExprKind::Lit(decode_lit(&list[1])?)
        }
        "var" => ExprKind::Var(SmolStr::new(atom_string(&list[1])?)),
        "string-new" => {
            if list.len() != 3 {
                return Err(SExprError::Invalid("(string-new r \"s\")".into()));
            }
            ExprKind::StringNew {
                region: SmolStr::new(atom_string(&list[1])?),
                value: unescape_string(atom_string(&list[2])?),
            }
        }
        "string-concat" => ExprKind::StringConcat {
            left: Box::new(decode_expr(&list[1])?),
            right: Box::new(decode_expr(&list[2])?),
        },
        "string-len" => ExprKind::StringLen(Box::new(decode_expr(&list[1])?)),
        "let" => ExprKind::Let {
            name: SmolStr::new(atom_string(&list[1])?),
            ty: None,
            value: Box::new(decode_expr(&list[2])?),
            body: Box::new(decode_expr(&list[3])?),
        },
        "letlin" => ExprKind::LetLin {
            name: SmolStr::new(atom_string(&list[1])?),
            ty: None,
            value: Box::new(decode_expr(&list[2])?),
            body: Box::new(decode_expr(&list[3])?),
        },
        "lambda" => ExprKind::Lambda {
            param: SmolStr::new(atom_string(&list[1])?),
            param_ty: decode_ty(&list[2])?,
            body: Box::new(decode_expr(&list[3])?),
        },
        "app" => ExprKind::App {
            func: Box::new(decode_expr(&list[1])?),
            arg: Box::new(decode_expr(&list[2])?),
        },
        "pair" => ExprKind::Pair {
            left: Box::new(decode_expr(&list[1])?),
            right: Box::new(decode_expr(&list[2])?),
        },
        "fst" => ExprKind::Fst(Box::new(decode_expr(&list[1])?)),
        "snd" => ExprKind::Snd(Box::new(decode_expr(&list[1])?)),
        "inl" => ExprKind::Inl {
            ty: decode_ty(&list[1])?,
            value: Box::new(decode_expr(&list[2])?),
        },
        "inr" => ExprKind::Inr {
            ty: decode_ty(&list[1])?,
            value: Box::new(decode_expr(&list[2])?),
        },
        "case" => {
            if list.len() != 4 {
                return Err(SExprError::Invalid("(case scr (x e1) (y e2))".into()));
            }
            let left = match &list[2] {
                SExpr::List(items) if items.len() == 2 => {
                    (SmolStr::new(atom_string(&items[0])?), decode_expr(&items[1])?)
                }
                _ => return Err(SExprError::Invalid("case branch must be (x body)".into())),
            };
            let right = match &list[3] {
                SExpr::List(items) if items.len() == 2 => {
                    (SmolStr::new(atom_string(&items[0])?), decode_expr(&items[1])?)
                }
                _ => return Err(SExprError::Invalid("case branch must be (x body)".into())),
            };
            ExprKind::Case {
                scrutinee: Box::new(decode_expr(&list[1])?),
                left_var: left.0,
                left_body: Box::new(left.1),
                right_var: right.0,
                right_body: Box::new(right.1),
            }
        }
        "if" => ExprKind::If {
            cond: Box::new(decode_expr(&list[1])?),
            then_branch: Box::new(decode_expr(&list[2])?),
            else_branch: Box::new(decode_expr(&list[3])?),
        },
        "region" => ExprKind::Region {
            name: SmolStr::new(atom_string(&list[1])?),
            body: Box::new(decode_expr(&list[2])?),
        },
        "borrow" => ExprKind::Borrow(Box::new(decode_expr(&list[1])?)),
        "deref" => ExprKind::Deref(Box::new(decode_expr(&list[1])?)),
        "drop" => ExprKind::Drop(Box::new(decode_expr(&list[1])?)),
        "copy" => ExprKind::Copy(Box::new(decode_expr(&list[1])?)),
        "block" => {
            let exprs = list[1..].iter().map(decode_expr).collect::<Result<Vec<_>, _>>()?;
            ExprKind::Block(exprs)
        }
        "binop" => ExprKind::BinOp {
            op: atom_to_binop(&list[1])?,
            left: Box::new(decode_expr(&list[2])?),
            right: Box::new(decode_expr(&list[3])?),
        },
        "unop" => ExprKind::UnaryOp {
            op: atom_to_unary(&list[1])?,
            operand: Box::new(decode_expr(&list[2])?),
        },
        _ => return Err(SExprError::Invalid(format!("unknown expr tag: {tag}"))),
    };
    Ok(Expr::dummy(kind))
}

fn lit_to_sexpr(lit: &Literal) -> SExpr {
    match lit {
        Literal::Unit => SExpr::Atom("unit".into()),
        Literal::Bool(v) => SExpr::List(vec![
            SExpr::Atom("bool".into()),
            SExpr::Atom(if *v { "true".into() } else { "false".into() }),
        ]),
        Literal::I32(v) => SExpr::List(vec![SExpr::Atom("i32".into()), SExpr::Atom(v.to_string())]),
        Literal::I64(v) => SExpr::List(vec![SExpr::Atom("i64".into()), SExpr::Atom(v.to_string())]),
        Literal::F32(v) => SExpr::List(vec![SExpr::Atom("f32".into()), SExpr::Atom(v.to_string())]),
        Literal::F64(v) => SExpr::List(vec![SExpr::Atom("f64".into()), SExpr::Atom(v.to_string())]),
        Literal::String(s) => SExpr::List(vec![SExpr::Atom("string".into()), SExpr::Atom(escape_string(s))]),
    }
}

fn decode_lit(expr: &SExpr) -> Result<Literal, SExprError> {
    match expr {
        SExpr::Atom(atom) if atom == "unit" => Ok(Literal::Unit),
        SExpr::List(items) if !items.is_empty() => {
            let tag = atom_string(&items[0])?;
            match tag.as_str() {
                "bool" => Ok(Literal::Bool(atom_string(&items[1])? == "true")),
                "i32" => Ok(Literal::I32(atom_string(&items[1])?.parse().map_err(|_| SExprError::Invalid("bad i32".into()))?)),
                "i64" => Ok(Literal::I64(atom_string(&items[1])?.parse().map_err(|_| SExprError::Invalid("bad i64".into()))?)),
                "f32" => Ok(Literal::F32(atom_string(&items[1])?.parse().map_err(|_| SExprError::Invalid("bad f32".into()))?)),
                "f64" => Ok(Literal::F64(atom_string(&items[1])?.parse().map_err(|_| SExprError::Invalid("bad f64".into()))?)),
                "string" => Ok(Literal::String(unescape_string(atom_string(&items[1])?))),
                _ => Err(SExprError::Invalid("unknown literal".into())),
            }
        }
        _ => Err(SExprError::Invalid("invalid literal".into())),
    }
}

fn ty_to_sexpr(ty: &Ty) -> SExpr {
    match ty {
        Ty::Base(b) => SExpr::List(vec![SExpr::Atom("base".into()), SExpr::Atom(base_to_atom(*b))]),
        Ty::String(r) => SExpr::List(vec![SExpr::Atom("string".into()), SExpr::Atom(escape_atom(r))]),
        Ty::Ref { linearity, inner } => SExpr::List(vec![
            SExpr::Atom("ref".into()),
            SExpr::Atom(match linearity {
                ephapax_syntax::Linearity::Linear => "linear".into(),
                ephapax_syntax::Linearity::Unrestricted => "unrestricted".into(),
            }),
            ty_to_sexpr(inner),
        ]),
        Ty::Fun { param, ret } => SExpr::List(vec![SExpr::Atom("fun".into()), ty_to_sexpr(param), ty_to_sexpr(ret)]),
        Ty::Prod { left, right } => SExpr::List(vec![SExpr::Atom("prod".into()), ty_to_sexpr(left), ty_to_sexpr(right)]),
        Ty::Sum { left, right } => SExpr::List(vec![SExpr::Atom("sum".into()), ty_to_sexpr(left), ty_to_sexpr(right)]),
        Ty::Region { name, inner } => SExpr::List(vec![
            SExpr::Atom("region-type".into()),
            SExpr::Atom(escape_atom(name)),
            ty_to_sexpr(inner),
        ]),
        Ty::Borrow(inner) => SExpr::List(vec![SExpr::Atom("borrow".into()), ty_to_sexpr(inner)]),
        Ty::Var(v) => SExpr::List(vec![SExpr::Atom("var".into()), SExpr::Atom(escape_atom(v))]),
        Ty::List(inner) => SExpr::List(vec![SExpr::Atom("list".into()), ty_to_sexpr(inner)]),
        Ty::Tuple(elem_types) => {
            let mut elems = vec![SExpr::Atom("tuple".into())];
            elems.extend(elem_types.iter().map(ty_to_sexpr));
            SExpr::List(elems)
        }
    }
}

fn decode_ty(expr: &SExpr) -> Result<Ty, SExprError> {
    let list = match expr {
        SExpr::List(items) => items,
        _ => return Err(SExprError::Invalid("expected type list".into())),
    };
    if list.is_empty() {
        return Err(SExprError::Invalid("empty type".into()));
    }
    let tag = atom_string(&list[0])?;
    match tag.as_str() {
        "base" => Ok(Ty::Base(atom_to_base(&list[1])?)),
        "string" => Ok(Ty::String(SmolStr::new(atom_string(&list[1])?))),
        "ref" => {
            let lin = atom_string(&list[1])?;
            let linearity = match lin.as_str() {
                "linear" => ephapax_syntax::Linearity::Linear,
                "unrestricted" => ephapax_syntax::Linearity::Unrestricted,
                _ => return Err(SExprError::Invalid("ref linearity".into())),
            };
            Ok(Ty::Ref {
                linearity,
                inner: Box::new(decode_ty(&list[2])?),
            })
        }
        "fun" => Ok(Ty::Fun {
            param: Box::new(decode_ty(&list[1])?),
            ret: Box::new(decode_ty(&list[2])?),
        }),
        "prod" => Ok(Ty::Prod {
            left: Box::new(decode_ty(&list[1])?),
            right: Box::new(decode_ty(&list[2])?),
        }),
        "sum" => Ok(Ty::Sum {
            left: Box::new(decode_ty(&list[1])?),
            right: Box::new(decode_ty(&list[2])?),
        }),
        "region-type" => Ok(Ty::Region {
            name: SmolStr::new(atom_string(&list[1])?),
            inner: Box::new(decode_ty(&list[2])?),
        }),
        "borrow" => Ok(Ty::Borrow(Box::new(decode_ty(&list[1])?))),
        "var" => Ok(Ty::Var(SmolStr::new(atom_string(&list[1])?))),
        _ => Err(SExprError::Invalid("unknown type tag".into())),
    }
}

fn base_to_atom(base: BaseTy) -> String {
    match base {
        BaseTy::Unit => "unit".into(),
        BaseTy::Bool => "bool".into(),
        BaseTy::I32 => "i32".into(),
        BaseTy::I64 => "i64".into(),
        BaseTy::F32 => "f32".into(),
        BaseTy::F64 => "f64".into(),
    }
}

fn atom_to_base(expr: &SExpr) -> Result<BaseTy, SExprError> {
    let atom = atom_string(expr)?;
    match atom.as_str() {
        "unit" => Ok(BaseTy::Unit),
        "bool" => Ok(BaseTy::Bool),
        "i32" => Ok(BaseTy::I32),
        "i64" => Ok(BaseTy::I64),
        "f32" => Ok(BaseTy::F32),
        "f64" => Ok(BaseTy::F64),
        _ => Err(SExprError::Invalid("unknown base type".into())),
    }
}

fn binop_to_atom(op: BinOp) -> String {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Mod => "mod",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::And => "and",
        BinOp::Or => "or",
    }
    .into()
}

fn atom_to_binop(expr: &SExpr) -> Result<BinOp, SExprError> {
    let atom = atom_string(expr)?;
    match atom.as_str() {
        "add" => Ok(BinOp::Add),
        "sub" => Ok(BinOp::Sub),
        "mul" => Ok(BinOp::Mul),
        "div" => Ok(BinOp::Div),
        "mod" => Ok(BinOp::Mod),
        "lt" => Ok(BinOp::Lt),
        "le" => Ok(BinOp::Le),
        "gt" => Ok(BinOp::Gt),
        "ge" => Ok(BinOp::Ge),
        "eq" => Ok(BinOp::Eq),
        "ne" => Ok(BinOp::Ne),
        "and" => Ok(BinOp::And),
        "or" => Ok(BinOp::Or),
        _ => Err(SExprError::Invalid("unknown binop".into())),
    }
}

fn unary_to_atom(op: UnaryOp) -> String {
    match op {
        UnaryOp::Not => "not",
        UnaryOp::Neg => "neg",
    }
    .into()
}

fn atom_to_unary(expr: &SExpr) -> Result<UnaryOp, SExprError> {
    let atom = atom_string(expr)?;
    match atom.as_str() {
        "not" => Ok(UnaryOp::Not),
        "neg" => Ok(UnaryOp::Neg),
        _ => Err(SExprError::Invalid("unknown unary op".into())),
    }
}

fn escape_atom(atom: &str) -> String {
    if atom.chars().all(|c| !c.is_whitespace() && c != '(' && c != ')' && c != '"') {
        atom.to_string()
    } else {
        escape_string(atom)
    }
}

fn escape_string(s: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

fn unescape_string(s: String) -> String {
    if !s.starts_with('"') {
        return s;
    }
    let mut chars = s.chars();
    chars.next();
    let mut out = String::new();
    let mut escape = false;
    while let Some(c) = chars.next() {
        if escape {
            out.push(match c {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '"' => '"',
                '\\' => '\\',
                other => other,
            });
            escape = false;
            continue;
        }
        if c == '\\' {
            escape = true;
            continue;
        }
        if c == '"' {
            break;
        }
        out.push(c);
    }
    out
}

fn atom_string(expr: &SExpr) -> Result<String, SExprError> {
    match expr {
        SExpr::Atom(s) => Ok(s.clone()),
        _ => Err(SExprError::Invalid("expected atom".into())),
    }
}

fn is_atom(expr: &SExpr, value: &str) -> bool {
    matches!(expr, SExpr::Atom(s) if s == value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_module() {
        let module = Module {
            name: SmolStr::new("test"),
            decls: vec![Decl::Fn {
                name: SmolStr::new("main"),
                params: vec![],
                ret_ty: Ty::Base(BaseTy::I32),
                body: Expr::dummy(ExprKind::Lit(Literal::I32(42))),
            }],
        };
        let sexpr = module_to_sexpr(&module);
        let parsed = module_from_sexpr(&sexpr).expect("parse");
        assert_eq!(module, parsed);
    }
}
