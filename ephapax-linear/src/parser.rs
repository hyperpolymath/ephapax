use crate::ast::{
    Affinity, ArenaDecl, BinaryOp, ContractClause, ContractKind, EffectDecl, EffectHandler,
    EffectImpl, EffectOp, Expr, FnModifier, Function, ImportClause, ImportDecl, Item, Literal,
    Module, Param, Statement, StructDecl, StructField, TypeExpr, UnaryOp,
};

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(source: &str) -> Result<Self, ParserError> {
        let lexer = Lexer::new(source);
        Ok(Self {
            tokens: lexer.tokens,
            pos: 0,
        })
    }

    pub fn parse_module(&mut self) -> Result<Module, ParserError> {
        let mut items = Vec::new();
        while !self.is_at_end() {
            if self.match_token(&Token::Semicolon) {
                continue;
            }
            items.push(self.parse_item()?);
        }
        Ok(Module { items })
    }

    fn parse_item(&mut self) -> Result<Item, ParserError> {
        let is_public = self.match_token(&Token::Pub);
        if self.match_token(&Token::Comptime) {
            return Ok(Item::Comptime(self.parse_block()?));
        }
        if self.match_token(&Token::Use) {
            return Ok(Item::Import(self.parse_import(is_public)?));
        }
        if self.match_token(&Token::Struct) {
            return Ok(Item::Struct(self.parse_struct(is_public)?));
        }
        if self.match_token(&Token::Effect) {
            return Ok(Item::Effect(self.parse_effect(is_public)?));
        }
        if self.match_token(&Token::Impl) {
            return Ok(Item::EffectImpl(self.parse_effect_impl()?));
        }
        if self.match_token(&Token::Let) {
            return Ok(Item::Arena(self.parse_arena()?));
        }
        Ok(Item::Function(self.parse_fn_decl(is_public)?))
    }

    fn parse_fn_decl(&mut self, is_public: bool) -> Result<Function, ParserError> {
        let mut modifiers = Vec::new();
        loop {
            if self.match_token(&Token::Async) {
                modifiers.push(FnModifier::Async);
                continue;
            }
            if self.match_token(&Token::Hash) {
                self.consume(Token::LBracket, "expected '[' after '#')")?;
                let attr = self.consume_ident("expected attribute")?;
                if attr != "safe" {
                    return Err(ParserError::Unexpected {
                        token: attr,
                        span: "attribute".into(),
                    });
                }
                self.consume(Token::RBracket, "expected ']' after attribute")?;
                modifiers.push(FnModifier::Safe);
                continue;
            }
            break;
        }
        self.consume(Token::Fn, "expected 'fn'")?;
        let name = self.consume_ident("expected function name")?;
        self.consume(Token::LParen, "expected '(' after fn name")?;
        let params = self.parse_param_list()?;
        self.consume(Token::RParen, "expected ') after params")?;
        let return_type = if self.match_token(&Token::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let contract = if self.match_token(&Token::Where) {
            self.parse_contract()?
        } else {
            Vec::new()
        };
        let body = self.parse_block()?;
        Ok(Function {
            name,
            modifiers,
            params,
            return_type,
            contract,
            body,
            is_public,
        })
    }

    fn parse_param_list(&mut self) -> Result<Vec<Param>, ParserError> {
        let mut params = Vec::new();
        if self.check(Token::RParen) {
            return Ok(params);
        }
        loop {
            let name = self.consume_ident("expected parameter name")?;
            self.consume(Token::Colon, "expected ':' after name")?;
            let ty = self.parse_type()?;
            let affinity = if self.match_token(&Token::Mut) {
                Affinity::Affine
            } else {
                Affinity::Linear
            };
            params.push(Param { name, affinity, ty });
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        Ok(params)
    }

    fn parse_type(&mut self) -> Result<TypeExpr, ParserError> {
        if self.match_token(&Token::LParen) {
            if self.match_token(&Token::RParen) {
                return Ok(TypeExpr::Unit);
            }
            let mut elements = vec![self.parse_type()?];
            while self.match_token(&Token::Comma) {
                elements.push(self.parse_type()?);
            }
            self.consume(Token::RParen, "expected ')' after tuple type")?;
            if elements.len() == 1 {
                return Ok(elements.into_iter().next().unwrap());
            }
            return Ok(TypeExpr::Tuple(elements));
        }
        if self.match_token(&Token::LBracket) {
            let inner = self.parse_type()?;
            self.consume(Token::RBracket, "expected ']'")?;
            return Ok(TypeExpr::Array(Box::new(inner)));
        }
        if self.match_token(&Token::LBrace) {
            let mut fields = Vec::new();
            while !self.check(Token::RBrace) {
                let name = self.consume_ident("expected record field name")?;
                self.consume(Token::Colon, "expected ':'")?;
                let ty = self.parse_type()?;
                fields.push((name, ty));
                if !self.match_token(&Token::Comma) {
                    break;
                }
            }
            self.consume(Token::RBrace, "expected '}'")?;
            return Ok(TypeExpr::Record(fields));
        }
        if self.match_token(&Token::Ampersand) {
            let mutable = self.match_token(&Token::Mut);
            let target = Box::new(self.parse_type()?);
            return Ok(TypeExpr::Reference { mutable, target });
        }
        if self.match_token(&Token::Effect) {
            self.consume(Token::Lt, "expected '<'")?;
            let inner = self.parse_type()?;
            self.consume(Token::Gt, "expected '>'")?;
            return Ok(TypeExpr::Effect(Box::new(inner)));
        }
        if let Some(Token::Ident(name)) = self.peek().cloned() {
            self.advance();
            return Ok(TypeExpr::Named(name));
        }
        Err(ParserError::Expected {
            expected: "type".into(),
            found: format!("{:?}", self.peek()),
            span: "type".into(),
        })
    }

    fn parse_contract(&mut self) -> Result<Vec<ContractClause>, ParserError> {
        let mut clauses = Vec::new();
        loop {
            let kind = if self.match_token(&Token::Pre) {
                ContractKind::Pre
            } else if self.match_token(&Token::Post) {
                ContractKind::Post
            } else if self.match_token(&Token::Invariant) {
                ContractKind::Invariant
            } else {
                return Err(ParserError::Unexpected {
                    token: format!("{:?}", self.peek()),
                    span: "contract clause".into(),
                });
            };
            self.consume(Token::Colon, "expected ':' after clause")?;
            let expr = self.parse_expression(0)?;
            clauses.push(ContractClause { kind, condition: expr });
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        Ok(clauses)
    }

    fn parse_struct(&mut self, is_public: bool) -> Result<StructDecl, ParserError> {
        let name = self.consume_ident("expected struct name")?;
        self.consume(Token::LBrace, "expected '{'")?;
        let mut fields = Vec::new();
        while !self.check(Token::RBrace) {
            let field_name = self.consume_ident("expected field name")?;
            self.consume(Token::Colon, "expected ':'")?;
            let ty = self.parse_type()?;
            fields.push(StructField { name: field_name, ty });
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        self.consume(Token::RBrace, "expected '}'")?;
        Ok(StructDecl { name, fields, is_public })
    }

    fn parse_effect(&mut self, is_public: bool) -> Result<EffectDecl, ParserError> {
        let name = self.consume_ident("expected effect name")?;
        self.consume(Token::LBrace, "expected '{'")?;
        let mut ops = Vec::new();
        while !self.check(Token::RBrace) {
            self.consume(Token::Fn, "expected 'fn'")?;
            let op_name = self.consume_ident("expected effect op")?;
            self.consume(Token::LParen, "expected '('")?;
            let params = self.parse_param_list()?;
            self.consume(Token::RParen, "expected ')'")?;
            let return_type = if self.match_token(&Token::Arrow) {
                Some(self.parse_type()?)
            } else {
                None
            };
            self.consume(Token::Semicolon, "expected ';'")?;
            ops.push(EffectOp { name: op_name, params, return_type });
        }
        self.consume(Token::RBrace, "expected '}'")?;
        Ok(EffectDecl { name, ops, is_public })
    }

    fn parse_effect_impl(&mut self) -> Result<EffectImpl, ParserError> {
        let effect = self.consume_ident("expected effect")?;
        self.consume(Token::LBrace, "expected '{'")?;
        let mut handlers = Vec::new();
        while !self.check(Token::RBrace) {
            self.consume(Token::Fn, "expected 'fn'")?;
            let name = self.consume_ident("expected handler name")?;
            self.consume(Token::LParen, "expected '('")?;
            let params = self.parse_param_list()?;
            self.consume(Token::RParen, "expected ')'")?;
            let return_type = if self.match_token(&Token::Arrow) {
                Some(self.parse_type()?)
            } else {
                None
            };
            let body = self.parse_block()?;
            handlers.push(EffectHandler { name, params, return_type, body });
        }
        self.consume(Token::RBrace, "expected '}'")?;
        Ok(EffectImpl { effect, handlers })
    }

    fn parse_import(&mut self, is_public: bool) -> Result<ImportDecl, ParserError> {
        let mut path = Vec::new();
        path.push(self.consume_ident("expected module")?);
        while self.check(Token::ColonColon)
            && !matches!(self.peek2(), Some(Token::Star) | Some(Token::LBrace))
        {
            self.consume(Token::ColonColon, "expected '::'")?;
            path.push(self.consume_ident("expected path segment")?);
        }
        let clause = if self.match_token(&Token::ColonColon) {
            if self.match_token(&Token::Star) {
                Some(ImportClause::Glob)
            } else if self.match_token(&Token::LBrace) {
                let mut items = Vec::new();
                loop {
                    let name = self.consume_ident("expected import item")?;
                    items.push(name);
                    if !self.match_token(&Token::Comma) {
                        break;
                    }
                }
                self.consume(Token::RBrace, "expected '}'")?;
                Some(ImportClause::Items(items))
            } else {
                None
            }
        } else {
            None
        };
        self.consume(Token::Semicolon, "expected ';'")?;
        Ok(ImportDecl { path, clause, is_public })
    }

    fn parse_arena(&mut self) -> Result<ArenaDecl, ParserError> {
        let name = self.consume_ident("expected arena name")?;
        self.consume(Token::Equal, "expected '='")?;
        self.consume(Token::Arena, "expected 'Arena'")?;
        self.consume(Token::ColonColon, "expected '::'")?;
        self.consume_ident("expected 'new'")?;
        self.consume(Token::LParen, "expected '('")?;
        self.consume(Token::RParen, "expected ')'")?;
        self.consume(Token::Semicolon, "expected ';'")?;
        Ok(ArenaDecl { name })
    }

    fn parse_block(&mut self) -> Result<Vec<Statement>, ParserError> {
        self.consume(Token::LBrace, "expected '{'")?;
        let mut statements = Vec::new();
        while !self.check(Token::RBrace) {
            statements.push(self.parse_statement()?);
        }
        self.consume(Token::RBrace, "expected '}'")?;
        Ok(statements)
    }

    fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        if self.match_token(&Token::Let) {
            if self.match_token(&Token::LParen) {
                let mut names = Vec::new();
                names.push(self.consume_ident("expected binding")?);
                while self.match_token(&Token::Comma) {
                    names.push(self.consume_ident("expected binding")?);
                }
                self.consume(Token::RParen, "expected ')'")?;
                self.consume(Token::Equal, "expected '='")?;
                let expr = self.parse_expression(0)?;
                self.consume(Token::Semicolon, "expected ';'")?;
                return Ok(Statement::Destructure { names, expr });
            }
            let affinity = if self.match_token(&Token::Mut) {
                Affinity::Affine
            } else {
                Affinity::Linear
            };
            let name = self.consume_ident("expected name")?;
            if self.match_token(&Token::Colon) {
                self.parse_type()?;
            }
            self.consume(Token::Equal, "expected '='")?;
            let expr = self.parse_expression(0)?;
            self.consume(Token::Semicolon, "expected ';'")?;
            return Ok(Statement::Let { name, expr, affinity });
        }
        if self.match_token(&Token::If) {
            let cond = self.parse_expression(0)?;
            let then_branch = self.parse_block()?;
            let else_branch = if self.match_token(&Token::Else) {
                Some(self.parse_block()?)
            } else {
                None
            };
            return Ok(Statement::If {
                cond,
                then_branch,
                else_branch,
            });
        }
        if self.match_token(&Token::While) {
            let cond = self.parse_expression(0)?;
            let body = self.parse_block()?;
            return Ok(Statement::While { cond, body });
        }
        if self.match_token(&Token::For) {
            let var = self.consume_ident("expected iterator name")?;
            self.consume(Token::In, "expected 'in'")?;
            let iterable = self.parse_expression(0)?;
            let body = self.parse_block()?;
            return Ok(Statement::For { var, iterable, body });
        }
        if self.match_token(&Token::Go) {
            return Ok(Statement::Go(self.parse_block()?));
        }
        if self.match_token(&Token::Return) {
            let expr = if !self.check(Token::Semicolon) {
                Some(self.parse_expression(0)?)
            } else {
                None
            };
            self.consume(Token::Semicolon, "expected ';'")?;
            return Ok(Statement::Return(expr));
        }
        if self.match_token(&Token::Await) {
            let expr = self.parse_expression(0)?;
            self.consume(Token::Semicolon, "expected ';'")?;
            return Ok(Statement::Await(expr));
        }
        if self.match_token(&Token::Try) {
            let expr = self.parse_expression(0)?;
            let propagate = self.match_token(&Token::Question);
            self.consume(Token::Semicolon, "expected ';'")?;
            return Ok(Statement::Try { expr, propagate });
        }
        if self.match_token(&Token::Comptime) {
            return Ok(Statement::Comptime(self.parse_block()?));
        }
        let expr = self.parse_expression(0)?;
        self.consume(Token::Semicolon, "expected ';'")?;
        Ok(Statement::Expr(expr))
    }

    fn parse_expression(&mut self, prec: u8) -> Result<Expr, ParserError> {
        let mut left = self.parse_prefix()?;
        while let Some(current_prec) = self.get_precedence() {
            if current_prec < prec {
                break;
            }
            let op = self.parse_binary_op()?;
            let right = self.parse_expression(current_prec + 1)?;
            left = match op {
                BinaryOp::Assign => match left {
                    Expr::Ident(name) => Expr::Assign { name, expr: Box::new(right) },
                    other => Expr::Assign {
                        name: format!("{:?}", other),
                        expr: Box::new(right),
                    },
                },
                _ => Expr::Binary(Box::new(left), op, Box::new(right)),
            };
        }
        Ok(left)
    }

    fn parse_prefix(&mut self) -> Result<Expr, ParserError> {
        if let Some(value) = self.match_number() {
            return Ok(Expr::Literal(Literal::Int(value)));
        }
        if let Some(value) = self.match_string_literal() {
            return Ok(Expr::Literal(Literal::Str(value)));
        }
        if self.match_token(&Token::True) {
            return Ok(Expr::Literal(Literal::Bool(true)));
        }
        if self.match_token(&Token::False) {
            return Ok(Expr::Literal(Literal::Bool(false)));
        }
        if self.match_token(&Token::Minus) {
            let expr = self.parse_prefix()?;
            return Ok(Expr::Unary(UnaryOp::Negate, Box::new(expr)));
        }
        if self.match_token(&Token::Bang) {
            let expr = self.parse_prefix()?;
            return Ok(Expr::Unary(UnaryOp::Not, Box::new(expr)));
        }
        if self.match_token(&Token::Restrict) {
            let expr = self.parse_expression(0)?;
            return Ok(Expr::Restrict(Box::new(expr)));
        }
        if self.match_token(&Token::Try) {
            let expr = self.parse_expression(0)?;
            return Ok(Expr::Try {
                expr: Box::new(expr),
                propagate: false,
            });
        }
        if self.match_token(&Token::LParen) {
            let expr = self.parse_expression(0)?;
            if self.match_token(&Token::Comma) {
                let mut tuple = vec![expr];
                while self.match_token(&Token::Comma) {
                    tuple.push(self.parse_expression(0)?);
                }
                self.consume(Token::RParen, "expected ')'")?;
                return Ok(Expr::Tuple(tuple));
            }
            self.consume(Token::RParen, "expected ')'")?;
            return Ok(expr);
        }
        if self.match_token(&Token::LBracket) {
            return Ok(Expr::Array(self.parse_array_literal()?));
        }
        if self.match_token(&Token::LBrace) {
            return Ok(Expr::Record(self.parse_record_literal()?));
        }
        if self.match_token(&Token::Pipe) {
            let mut params = Vec::new();
            while !self.check(Token::Pipe) {
                let name = self.consume_ident("expected lambda param")?;
                let ty = if self.match_token(&Token::Colon) {
                    self.parse_type()?
                } else {
                    TypeExpr::Named("_".into())
                };
                params.push(Param {
                    name,
                    affinity: Affinity::Linear,
                    ty,
                });
                if !self.match_token(&Token::Comma) {
                    break;
                }
            }
            self.consume(Token::Pipe, "expected '|'")?;
            let body = self.parse_expression(0)?;
            return Ok(Expr::Block(vec![Statement::Expr(body)]));
        }
        if let Some(name) = self.match_ident() {
            return self.parse_postfix(Expr::Ident(name));
        }
        Err(ParserError::Unexpected {
            token: format!("{:?}", self.peek()),
            span: "expression".into(),
        })
    }

    fn match_number(&mut self) -> Option<i64> {
        if let Some(Token::Number(value)) = self.peek().cloned() {
            self.advance();
            return Some(value);
        }
        None
    }

    fn match_string_literal(&mut self) -> Option<String> {
        if let Some(Token::StringLiteral(value)) = self.peek().cloned() {
            self.advance();
            return Some(value);
        }
        None
    }

    fn parse_postfix(&mut self, mut expr: Expr) -> Result<Expr, ParserError> {
        loop {
            if self.match_token(&Token::Dot) {
                let field = self.consume_ident("expected field name")?;
                expr = Expr::FieldAccess {
                    target: Box::new(expr),
                    field,
                };
                continue;
            }
            if self.match_token(&Token::LParen) {
                let args = self.parse_argument_list()?;
                self.consume(Token::RParen, "expected ')'")?;
                expr = Expr::Call {
                    callee: Box::new(expr),
                    args,
                };
                continue;
            }
            if self.match_token(&Token::LBracket) {
                let index = self.parse_expression(0)?;
                self.consume(Token::RBracket, "expected ']'")?;
                expr = Expr::Index {
                    target: Box::new(expr),
                    index: Box::new(index),
                };
                continue;
            }
            break;
        }
        Ok(expr)
    }

    fn parse_argument_list(&mut self) -> Result<Vec<Expr>, ParserError> {
        let mut args = Vec::new();
        if self.check(Token::RParen) {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expression(0)?);
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        Ok(args)
    }

    fn parse_array_literal(&mut self) -> Result<Vec<Expr>, ParserError> {
        let mut elements = Vec::new();
        if self.check(Token::RBracket) {
            self.advance();
            return Ok(elements);
        }
        loop {
            elements.push(self.parse_expression(0)?);
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        self.consume(Token::RBracket, "expected ']'")?;
        Ok(elements)
    }

    fn parse_record_literal(&mut self) -> Result<Vec<(String, Expr)>, ParserError> {
        let mut entries = Vec::new();
        if self.check(Token::RBrace) {
            self.advance();
            return Ok(entries);
        }
        loop {
            let name = self.consume_ident("expected record field")?;
            self.consume(Token::Colon, "expected ':'")?;
            let value = self.parse_expression(0)?;
            entries.push((name, value));
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        self.consume(Token::RBrace, "expected '}'")?;
        Ok(entries)
    }

    fn parse_binary_op(&mut self) -> Result<BinaryOp, ParserError> {
        if self.match_token(&Token::Equal) {
            return Ok(BinaryOp::Assign);
        }
        if self.match_token(&Token::Plus) {
            return Ok(BinaryOp::Add);
        }
        if self.match_token(&Token::Minus) {
            return Ok(BinaryOp::Sub);
        }
        if self.match_token(&Token::Star) {
            return Ok(BinaryOp::Multiply);
        }
        if self.match_token(&Token::Slash) {
            return Ok(BinaryOp::Divide);
        }
        if self.match_token(&Token::Percent) {
            return Ok(BinaryOp::Multiply);
        }
        if self.match_token(&Token::EqualEqual) {
            return Ok(BinaryOp::Equal);
        }
        if self.match_token(&Token::BangEqual) {
            return Ok(BinaryOp::NotEqual);
        }
        if self.match_token(&Token::Lt) {
            return Ok(BinaryOp::Lt);
        }
        if self.match_token(&Token::Gt) {
            return Ok(BinaryOp::Gt);
        }
        if self.match_token(&Token::Lte) {
            return Ok(BinaryOp::Lte);
        }
        if self.match_token(&Token::Gte) {
            return Ok(BinaryOp::Gte);
        }
        if self.match_token(&Token::AndAnd) {
            return Ok(BinaryOp::And);
        }
        if self.match_token(&Token::OrOr) {
            return Ok(BinaryOp::Or);
        }
        if self.match_token(&Token::Range) {
            return Ok(BinaryOp::Range);
        }
        Err(ParserError::Unexpected {
            token: format!("{:?}", self.peek()),
            span: "binary operator".into(),
        })
    }

    fn get_precedence(&self) -> Option<u8> {
        match self.peek() {
            Some(Token::OrOr) => Some(1),
            Some(Token::AndAnd) => Some(2),
            Some(Token::EqualEqual) | Some(Token::BangEqual) => Some(3),
            Some(Token::Lt) | Some(Token::Gt) | Some(Token::Lte) | Some(Token::Gte) => Some(4),
            Some(Token::Plus) | Some(Token::Minus) => Some(5),
            Some(Token::Star) | Some(Token::Slash) | Some(Token::Percent) => Some(6),
            Some(Token::Range) => Some(0),
            Some(Token::Equal) => Some(0),
            _ => None,
        }
    }

    fn consume_ident(&mut self, message: &str) -> Result<String, ParserError> {
        if let Some(Token::Ident(name)) = self.peek().cloned() {
            self.advance();
            return Ok(name);
        }
        Err(ParserError::Expected {
            expected: "identifier".into(),
            found: format!("{:?}", self.peek()),
            span: message.into(),
        })
    }

    fn match_token(&mut self, expected: &Token) -> bool {
        if self.check(expected.clone()) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn check(&self, expected: Token) -> bool {
        matches!(self.peek(), Some(token) if token == &expected)
    }

    fn consume(&mut self, expected: Token, message: &str) -> Result<(), ParserError> {
        if self.check(expected.clone()) {
            self.advance();
            Ok(())
        } else {
            Err(ParserError::Expected {
                expected: format!("{:?}", expected),
                found: format!("{:?}", self.peek()),
                span: message.into(),
            })
        }
    }

    fn match_ident(&mut self) -> Option<String> {
        if let Some(Token::Ident(name)) = self.peek().cloned() {
            self.advance();
            Some(name)
        } else {
            None
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) -> Option<&Token> {
        if !self.is_at_end() {
            let token = &self.tokens[self.pos];
            self.pos += 1;
            Some(token)
        } else {
            None
        }
    }

    fn is_at_end(&self) -> bool {
        matches!(self.peek(), Some(Token::Eof))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Fn,
    Struct,
    Effect,
    Impl,
    Pub,
    Use,
    Arena,
    Async,
    Comptime,
    Let,
    Mut,
    If,
    Else,
    Go,
    While,
    For,
    In,
    Return,
    Await,
    Try,
    Restrict,
    True,
    False,
    Pre,
    Post,
    Invariant,
    Where,
    Ident(String),
    Number(i64),
    StringLiteral(String),
    Equal,
    EqualEqual,
    Bang,
    BangEqual,
    Lt,
    Gt,
    Lte,
    Gte,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Ampersand,
    AndAnd,
    OrOr,
    Pipe,
    Question,
    Semicolon,
    Colon,
    ColonColon,
    Comma,
    Dot,
    Range,
    Arrow,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Hash,
    Eof,
}

pub struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    pub tokens: Vec<Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut lexer = Self {
            chars: source.chars().peekable(),
            tokens: Vec::new(),
        };
        lexer.lex();
        lexer
    }

    fn lex(&mut self) {
        while let Some(&ch) = self.chars.peek() {
            match ch {
                c if c.is_whitespace() => {
                    self.chars.next();
                }
                '{' => {
                    self.tokens.push(Token::LBrace);
                    self.chars.next();
                }
                '}' => {
                    self.tokens.push(Token::RBrace);
                    self.chars.next();
                }
                '(' => {
                    self.tokens.push(Token::LParen);
                    self.chars.next();
                }
                ')' => {
                    self.tokens.push(Token::RParen);
                    self.chars.next();
                }
                '[' => {
                    self.tokens.push(Token::LBracket);
                    self.chars.next();
                }
                ']' => {
                    self.tokens.push(Token::RBracket);
                    self.chars.next();
                }
                ';' => {
                    self.tokens.push(Token::Semicolon);
                    self.chars.next();
                }
                ',' => {
                    self.tokens.push(Token::Comma);
                    self.chars.next();
                }
                ':' => {
                    self.chars.next();
                    if self.match_next(':') {
                        self.tokens.push(Token::ColonColon);
                    } else {
                        self.tokens.push(Token::Colon);
                    }
                }
                '+' => {
                    self.tokens.push(Token::Plus);
                    self.chars.next();
                }
                '-' => {
                    self.chars.next();
                    if self.match_next('>') {
                        self.tokens.push(Token::Arrow);
                    } else {
                        self.tokens.push(Token::Minus);
                    }
                }
                '*' => {
                    self.tokens.push(Token::Star);
                    self.chars.next();
                }
                '%' => {
                    self.tokens.push(Token::Percent);
                    self.chars.next();
                }
                '&' => {
                    self.chars.next();
                    if self.match_next('&') {
                        self.tokens.push(Token::AndAnd);
                    } else {
                        self.tokens.push(Token::Ampersand);
                    }
                }
                '|' => {
                    self.chars.next();
                    if self.match_next('|') {
                        self.tokens.push(Token::OrOr);
                    } else {
                        self.tokens.push(Token::Pipe);
                    }
                }
                '=' => {
                    self.chars.next();
                    if self.match_next('=') {
                        self.tokens.push(Token::EqualEqual);
                    } else {
                        self.tokens.push(Token::Equal);
                    }
                }
                '!' => {
                    self.chars.next();
                    if self.match_next('=') {
                        self.tokens.push(Token::BangEqual);
                    } else {
                        self.tokens.push(Token::Bang);
                    }
                }
                '<' => {
                    self.chars.next();
                    if self.match_next('=') {
                        self.tokens.push(Token::Lte);
                    } else {
                        self.tokens.push(Token::Lt);
                    }
                }
                '>' => {
                    self.chars.next();
                    if self.match_next('=') {
                        self.tokens.push(Token::Gte);
                    } else {
                        self.tokens.push(Token::Gt);
                    }
                }
                '.' => {
                    self.chars.next();
                    if self.match_next('.') {
                        self.tokens.push(Token::Range);
                    } else {
                        self.tokens.push(Token::Dot);
                    }
                }
                '?' => {
                    self.tokens.push(Token::Question);
                    self.chars.next();
                }
                '/' => {
                    self.chars.next();
                    if self.match_next('/') {
                        self.skip_line_comment();
                    } else if self.match_next('*') {
                        self.skip_block_comment();
                    } else {
                        self.tokens.push(Token::Slash);
                    }
                }
                '#' => {
                    self.tokens.push(Token::Hash);
                    self.chars.next();
                }
                '"' => {
                    self.chars.next();
                    let value = self.read_string_literal();
                    self.tokens.push(Token::StringLiteral(value));
                }
                c if c.is_ascii_digit() => {
                    let num = self.read_number();
                    self.tokens.push(Token::Number(num));
                }
                c if c.is_ascii_alphanumeric() || c == '_' => {
                    let ident = self.read_ident();
                    self.tokens.push(self.keyword_or_ident(ident));
                }
                _ => {
                    self.chars.next();
                }
            }
        }
        self.tokens.push(Token::Eof);
    }

    fn keyword_or_ident(&self, ident: String) -> Token {
        match ident.as_str() {
            "fn" => Token::Fn,
            "struct" => Token::Struct,
            "effect" => Token::Effect,
            "impl" => Token::Impl,
            "pub" => Token::Pub,
            "use" => Token::Use,
            "arena" => Token::Arena,
            "async" => Token::Async,
            "comptime" => Token::Comptime,
            "let" => Token::Let,
            "mut" => Token::Mut,
            "if" => Token::If,
            "else" => Token::Else,
            "go" => Token::Go,
            "while" => Token::While,
            "for" => Token::For,
            "in" => Token::In,
            "return" => Token::Return,
            "await" => Token::Await,
            "try" => Token::Try,
            "restrict" => Token::Restrict,
            "true" => Token::True,
            "false" => Token::False,
            "where" => Token::Where,
            "pre" => Token::Pre,
            "post" => Token::Post,
            "invariant" => Token::Invariant,
            _ => Token::Ident(ident),
        }
    }

    fn match_next(&mut self, expected: char) -> bool {
        if let Some(&next) = self.chars.peek() {
            if next == expected {
                self.chars.next();
                return true;
            }
        }
        false
    }

    fn skip_line_comment(&mut self) {
        while let Some(&ch) = self.chars.peek() {
            if ch == '\n' {
                break;
            }
            self.chars.next();
        }
    }

    fn skip_block_comment(&mut self) {
        while let Some(ch) = self.chars.next() {
            if ch == '*' && self.match_next('/') {
                break;
            }
        }
    }

    fn read_number(&mut self) -> i64 {
        let mut digits = String::new();
        while let Some(&ch) = self.chars.peek() {
            if ch.is_ascii_digit() {
                digits.push(ch);
                self.chars.next();
            } else {
                break;
            }
        }
        digits.parse().unwrap_or(0)
    }

    fn read_ident(&mut self) -> String {
        let mut ident = String::new();
        while let Some(&ch) = self.chars.peek() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ident.push(ch);
                self.chars.next();
            } else {
                break;
            }
        }
        ident
    }

    fn read_string_literal(&mut self) -> String {
        let mut value = String::new();
        while let Some(ch) = self.chars.next() {
            match ch {
                '\\' => {
                    if let Some(escaped) = self.chars.next() {
                        match escaped {
                            'n' => value.push('\n'),
                            'r' => value.push('\r'),
                            't' => value.push('\t'),
                            '\\' => value.push('\\'),
                            '"' => value.push('"'),
                            other => value.push(other),
                        }
                    }
                }
                '"' => break,
                other => value.push(other),
            }
        }
        value
    }
}

#[derive(Debug)]
pub enum ParserError {
    Unexpected { token: String, span: String },
    Expected { expected: String, found: String, span: String },
}
