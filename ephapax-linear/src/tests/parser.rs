use crate::ast::{Item, Statement};
use crate::parser::Parser;

#[test]
fn parse_function_and_statements() {
    let source = r#"
        fn main() {
            let mut token: Int = 1;
            let value = token;
            return value;
        }
    "#;

    let mut parser = Parser::new(source).unwrap();
    let module = parser.parse_module().unwrap();
    assert_eq!(module.items.len(), 1);

    match &module.items[0] {
        Item::Function(func) => {
            assert_eq!(func.name, "main");
            assert_eq!(func.body.len(), 3);
            assert!(matches!(func.body[0], Statement::Let { .. }));
        }
        _ => panic!("expected function"),
    }
}

#[test]
fn parse_struct_and_effect() {
    let source = r#"
        struct Point {
            x: Int,
            y: Int,
        }

        effect Console {
            fn print(msg: String);
        }
    "#;

    let mut parser = Parser::new(source).unwrap();
    let module = parser.parse_module().unwrap();
    assert_eq!(module.items.len(), 2);
    assert!(matches!(module.items[0], Item::Struct(_)));
    assert!(matches!(module.items[1], Item::Effect(_)));
}

#[test]
fn parse_import_and_arena() {
    let source = r#"
        use utils::math::{add, sub};
        let arena = Arena::new();
    "#;

    let mut parser = Parser::new(source).unwrap();
    let module = parser.parse_module().unwrap();
    assert!(matches!(module.items[0], Item::Import(_)));
    assert!(matches!(module.items[1], Item::Arena(_)));
}
