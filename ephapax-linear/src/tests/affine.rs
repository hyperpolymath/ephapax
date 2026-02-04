use crate::ast::{Affinity, Expr, Function, Item, Literal, Module, Statement};
use crate::interpreter::{Diagnostic, Interpreter};

fn linear_function() -> Function {
    Function {
        name: "linear_consume".into(),
        modifiers: Vec::new(),
        params: Vec::new(),
        return_type: None,
        contract: Vec::new(),
        body: vec![
            Statement::Let {
                name: "token".into(),
                expr: Expr::Literal(Literal::Int(10)),
                affinity: Affinity::Linear,
            },
            Statement::Let {
                name: "copy".into(),
                expr: Expr::Literal(Literal::Int(20)),
                affinity: Affinity::Affine,
            },
            Statement::Expr(Expr::Assign {
                name: "token".into(),
                expr: Box::new(Expr::Literal(Literal::Int(11))),
            }),
        ],
        is_public: false,
    }
}

#[test]
fn linear_reassignment_blocked() {
    let module = Module {
        items: vec![Item::Function(linear_function())],
    };

    let mut interpreter = Interpreter::new();
    let err = interpreter.run(&module).unwrap_err();
    assert!(
        matches!(err, Diagnostic::LinearReassignment { .. }),
        "expected linear reassignment diagnostic, got {:?}",
        err
    );
}
