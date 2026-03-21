use crate::ast::{Affinity, Expr, Function, Item, Module, Statement};

pub struct Binding {
    pub affinity: Affinity,
    pub used: bool,
}

#[derive(Debug, Clone)]
pub enum Diagnostic {
    LinearReassignment { name: String },
    UnusedLinear { name: String },
    UndefinedVariable { name: String },
}

pub struct Interpreter {
    pub linear_state: Vec<String>,
    pub bindings: std::collections::HashMap<String, Binding>,
    pub diagnostics: Vec<Diagnostic>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            linear_state: Vec::new(),
            bindings: std::collections::HashMap::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn run(&mut self, module: &Module) -> Result<(), Diagnostic> {
        for item in &module.items {
            if let Item::Function(func) = item {
                self.bindings.clear();
                self.execute_function(func)?;
                self.check_unused_linear()?;
            }
        }
        Ok(())
    }

    fn execute_function(&mut self, function: &Function) -> Result<(), Diagnostic> {
        self.linear_state.push(function.name.clone());
        for stmt in &function.body {
            self.execute_statement(stmt)?;
        }
        self.linear_state.pop();
        Ok(())
    }

    fn execute_statement(&mut self, stmt: &Statement) -> Result<(), Diagnostic> {
        match stmt {
            Statement::Expr(expr) => self.evaluate(expr),
            Statement::Let { name, expr, affinity } => {
                self.evaluate(expr)?;
                if let Affinity::Linear = affinity {
                    if self.bindings.contains_key(name) {
                        let diag = Diagnostic::LinearReassignment { name: name.clone() };
                        self.diagnostics.push(diag.clone());
                        return Err(diag);
                    }
                }
                self.bindings.insert(
                    name.clone(),
                    Binding {
                        affinity: affinity.clone(),
                        used: false,
                    },
                );
                Ok(())
            }
            Statement::Destructure { expr, names } => {
                self.evaluate(expr)?;
                for name in names {
                    self.bindings
                        .entry(name.clone())
                        .or_insert(Binding { affinity: Affinity::Linear, used: false });
                }
                Ok(())
            }
            Statement::Return(expr) => {
                if let Some(e) = expr {
                    self.evaluate(e)?;
                }
                Ok(())
            }
            Statement::If { cond, then_branch, else_branch } => {
                self.evaluate(cond)?;
                for stmt in then_branch {
                    self.execute_statement(stmt)?;
                }
                if let Some(branch) = else_branch {
                    for stmt in branch {
                        self.execute_statement(stmt)?;
                    }
                }
                Ok(())
            }
            Statement::While { cond, body } => {
                self.evaluate(cond)?;
                for stmt in body {
                    self.execute_statement(stmt)?;
                }
                Ok(())
            }
            Statement::For { iterable, body, .. } => {
                self.evaluate(iterable)?;
                for stmt in body {
                    self.execute_statement(stmt)?;
                }
                Ok(())
            }
            Statement::Go(body) => {
                for stmt in body {
                    self.execute_statement(stmt)?;
                }
                Ok(())
            }
            Statement::Await(expr) => self.evaluate(expr),
            Statement::Try { expr, .. } => self.evaluate(expr),
            Statement::Comptime(body) | Statement::Block(body) => {
                for stmt in body {
                    self.execute_statement(stmt)?;
                }
                Ok(())
            }
        }
    }

    fn evaluate(&mut self, expr: &Expr) -> Result<(), Diagnostic> {
        match expr {
            Expr::Literal(_) => Ok(()),
            Expr::Ident(name) => {
                self.mark_used(name);
                if self.bindings.contains_key(name) {
                    Ok(())
                } else {
                    let diag = Diagnostic::UndefinedVariable { name: name.clone() };
                    self.diagnostics.push(diag.clone());
                    Err(diag)
                }
            }
            Expr::Unary(_, operand) => self.evaluate(operand),
            Expr::Binary(left, _, right) => {
                self.evaluate(left)?;
                self.evaluate(right)
            }
            Expr::Assign { name, expr } => {
                self.evaluate(expr)?;
                if let Some(binding) = self.bindings.get(name) {
                    if matches!(binding.affinity, Affinity::Linear) {
                        let diag = Diagnostic::LinearReassignment { name: name.clone() };
                        self.diagnostics.push(diag.clone());
                        return Err(diag);
                    }
                } else {
                    let diag = Diagnostic::UndefinedVariable { name: name.clone() };
                    self.diagnostics.push(diag.clone());
                    return Err(diag);
                }
                Ok(())
            }
            Expr::Call { callee, args } => {
                self.evaluate(callee)?;
                for arg in args {
                    self.evaluate(arg)?;
                }
                Ok(())
            }
            Expr::FieldAccess { target, .. } => self.evaluate(target),
            Expr::Index { target, index } => {
                self.evaluate(target)?;
                self.evaluate(index)
            }
            Expr::Array(elements) => {
                for element in elements {
                    self.evaluate(element)?;
                }
                Ok(())
            }
            Expr::Record(fields) => {
                for (_, value) in fields {
                    self.evaluate(value)?;
                }
                Ok(())
            }
            Expr::Tuple(items) => {
                for item in items {
                    self.evaluate(item)?;
                }
                Ok(())
            }
            Expr::Block(statements) => {
                for stmt in statements {
                    self.execute_statement(stmt)?;
                }
                Ok(())
            }
            Expr::Range(start, end) => {
                self.evaluate(start)?;
                self.evaluate(end)
            }
            Expr::Restrict(inner) => self.evaluate(inner),
            Expr::Try { expr, .. } => self.evaluate(expr),
        }
    }

    fn mark_used(&mut self, name: &str) {
        if let Some(binding) = self.bindings.get_mut(name) {
            binding.used = true;
        }
    }

    fn check_unused_linear(&mut self) -> Result<(), Diagnostic> {
        for (name, binding) in &self.bindings {
            if matches!(binding.affinity, Affinity::Linear) && !binding.used {
                let diag = Diagnostic::UnusedLinear { name: name.clone() };
                self.diagnostics.push(diag.clone());
                return Err(diag);
            }
        }
        Ok(())
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}
