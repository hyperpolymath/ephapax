use std::collections::{HashMap, HashSet};

use crate::ast::{
    Affinity, ContractClause, ContractKind, Expr, Function, Item, Module, Param, Statement, TypeExpr,
};

pub struct TypeChecker {
    pub diagnostics: Vec<TypeDiagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDiagnostic {
    DuplicateFunction { name: String },
    DuplicateStruct { name: String },
    DuplicateEffect { name: String },
    UndefinedIdentifier { name: String, function: String },
    LinearNotUsed { name: String, function: String },
    LinearReassignment { name: String, function: String },
    ContractNotBool { function: String, kind: ContractKind },
}

struct FunctionContext {
    env: HashMap<String, Affinity>,
    linear_decl: HashSet<String>,
    linear_used: HashSet<String>,
    function: String,
}

impl FunctionContext {
    fn new(function: &Function) -> Self {
        Self {
            env: HashMap::new(),
            linear_decl: HashSet::new(),
            linear_used: HashSet::new(),
            function: function.name.clone(),
        }
    }

    fn declare(&mut self, name: &str, affinity: Affinity) {
        self.env.insert(name.into(), affinity.clone());
        if matches!(affinity, Affinity::Linear) {
            self.linear_decl.insert(name.into());
        }
    }

    fn mark_used(&mut self, name: &str) {
        if self.env.get(name) == Some(&Affinity::Linear) {
            self.linear_used.insert(name.into());
        }
    }

    fn is_defined(&self, name: &str) -> bool {
        self.env.contains_key(name)
    }
}

#[derive(Debug, Clone, Copy)]
enum ExprKind {
    Bool,
    Other,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
        }
    }

    pub fn check_module(&mut self, module: &Module) -> Result<(), TypeDiagnostic> {
        let mut functions = HashSet::new();
        let mut structs = HashSet::new();
        let mut effects = HashSet::new();

        for item in &module.items {
            match item {
                Item::Function(func) => {
                    if !functions.insert(func.name.clone()) {
                        return self.emit(TypeDiagnostic::DuplicateFunction {
                            name: func.name.clone(),
                        });
                    }
                    self.check_function(func)?;
                }
                Item::Struct(struct_decl) => {
                    if !structs.insert(struct_decl.name.clone()) {
                        return self.emit(TypeDiagnostic::DuplicateStruct {
                            name: struct_decl.name.clone(),
                        });
                    }
                }
                Item::Effect(effect) => {
                    if !effects.insert(effect.name.clone()) {
                        return self.emit(TypeDiagnostic::DuplicateEffect {
                            name: effect.name.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn check_function(&mut self, func: &Function) -> Result<(), TypeDiagnostic> {
        let mut ctx = FunctionContext::new(func);
        for param in &func.params {
            ctx.declare(&param.name, param.affinity.clone());
        }
        for clause in &func.contract {
            self.check_contract_clause(&mut ctx, clause, func)?;
        }
        for stmt in &func.body {
            self.check_statement(stmt, &mut ctx)?;
        }
        for name in ctx.linear_decl.difference(&ctx.linear_used) {
            return self.emit(TypeDiagnostic::LinearNotUsed {
                name: name.clone(),
                function: func.name.clone(),
            });
        }
        Ok(())
    }

    fn check_contract_clause(
        &mut self,
        ctx: &mut FunctionContext,
        clause: &ContractClause,
        func: &Function,
    ) -> Result<(), TypeDiagnostic> {
        let kind = clause.kind.clone();
        let kind_name = kind.clone();
        let expr_kind = self.check_expr(ctx, &clause.condition)?;
        if expr_kind != ExprKind::Bool {
            return self.emit(TypeDiagnostic::ContractNotBool {
                function: func.name.clone(),
                kind: kind_name,
            });
        }
        Ok(())
    }

    fn check_statement(
        &mut self,
        stmt: &Statement,
        ctx: &mut FunctionContext,
    ) -> Result<(), TypeDiagnostic> {
        match stmt {
            Statement::Expr(expr) => {
                self.check_expr(ctx, expr)?;
            }
            Statement::Let { name, expr, affinity } => {
                self.check_expr(ctx, expr)?;
                if ctx.is_defined(name) && matches!(affinity, Affinity::Linear) {
                    return self.emit(TypeDiagnostic::LinearReassignment {
                        name: name.clone(),
                        function: ctx.function.clone(),
                    });
                }
                ctx.declare(name, affinity.clone());
            }
            Statement::Destructure { names, expr } => {
                self.check_expr(ctx, expr)?;
                for name in names {
                    ctx.declare(name, Affinity::Linear);
                }
            }
            Statement::Return(expr) => {
                if let Some(e) = expr {
                    self.check_expr(ctx, e)?;
                }
            }
            Statement::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.check_expr(ctx, cond)?;
                for stmt in then_branch {
                    self.check_statement(stmt, ctx)?;
                }
                if let Some(branch) = else_branch {
                    for stmt in branch {
                        self.check_statement(stmt, ctx)?;
                    }
                }
            }
            Statement::While { cond, body } => {
                self.check_expr(ctx, cond)?;
                for stmt in body {
                    self.check_statement(stmt, ctx)?;
                }
            }
            Statement::For { iterable, body, .. } => {
                self.check_expr(ctx, iterable)?;
                for stmt in body {
                    self.check_statement(stmt, ctx)?;
                }
            }
            Statement::Go(body) | Statement::Block(body) | Statement::Comptime(body) => {
                for stmt in body {
                    self.check_statement(stmt, ctx)?;
                }
            }
            Statement::Await(expr) | Statement::Try { expr, .. } => {
                self.check_expr(ctx, expr)?;
            }
        }
        Ok(())
    }

    fn check_expr(
        &mut self,
        ctx: &mut FunctionContext,
        expr: &Expr,
    ) -> Result<ExprKind, TypeDiagnostic> {
        match expr {
            Expr::Literal(Literal::Bool(_)) => Ok(ExprKind::Bool),
            Expr::Literal(_) => Ok(ExprKind::Other),
            Expr::Ident(name) => {
                if !ctx.is_defined(name) {
                    return self.emit(TypeDiagnostic::UndefinedIdentifier {
                        name: name.clone(),
                        function: ctx.function.clone(),
                    });
                }
                ctx.mark_used(name);
                Ok(ExprKind::Other)
            }
            Expr::Unary(_, operand) => self.check_expr(ctx, operand),
            Expr::Binary(_, op, right) => {
                let left_kind = self.check_expr(ctx, right)?;
                let right_kind = self.check_expr(ctx, right)?;
                match op {
                    BinaryOp::Equal
                    | BinaryOp::NotEqual
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Lte
                    | BinaryOp::Gte
                    | BinaryOp::And
                    | BinaryOp::Or => Ok(ExprKind::Bool),
                    _ => Ok(ExprKind::Other),
                }
            }
            Expr::Call { callee, args } => {
                self.check_expr(ctx, callee)?;
                for arg in args {
                    self.check_expr(ctx, arg)?;
                }
                Ok(ExprKind::Other)
            }
            Expr::Assign { name, expr } => {
                self.check_expr(ctx, expr)?;
                if !ctx.is_defined(name) {
                    return self.emit(TypeDiagnostic::UndefinedIdentifier {
                        name: name.clone(),
                        function: ctx.function.clone(),
                    });
                }
                if ctx.env.get(name) == Some(&Affinity::Linear) {
                    return self.emit(TypeDiagnostic::LinearReassignment {
                        name: name.clone(),
                        function: ctx.function.clone(),
                    });
                }
                Ok(ExprKind::Other)
            }
            Expr::FieldAccess { target, .. } => {
                self.check_expr(ctx, target)?;
                Ok(ExprKind::Other)
            }
            Expr::Index { target, index } => {
                self.check_expr(ctx, target)?;
                self.check_expr(ctx, index)?;
                Ok(ExprKind::Other)
            }
            Expr::Array(elements) | Expr::Tuple(elements) => {
                for element in elements {
                    self.check_expr(ctx, element)?;
                }
                Ok(ExprKind::Other)
            }
            Expr::Record(fields) => {
                for (_, value) in fields {
                    self.check_expr(ctx, value)?;
                }
                Ok(ExprKind::Other)
            }
            Expr::Block(statements) => {
                for stmt in statements {
                    self.check_statement(stmt, ctx)?;
                }
                Ok(ExprKind::Other)
            }
            Expr::Range(start, end) => {
                self.check_expr(ctx, start)?;
                self.check_expr(ctx, end)?;
                Ok(ExprKind::Other)
            }
            Expr::Restrict(inner) | Expr::Try { expr: inner, .. } => self.check_expr(ctx, inner),
        }
    }

    fn emit(&mut self, diag: TypeDiagnostic) -> Result<(), TypeDiagnostic> {
        self.diagnostics.push(diag.clone());
        Err(diag)
    }
}
