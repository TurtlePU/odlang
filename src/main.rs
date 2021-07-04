use bindings::Bindings;

use ast::*;

mod ast;
mod bindings;

fn main() {
    dbg!(Bindings::from(&vec![Decl::TopLevelValue(Binding {
        name: Name::from("main"),
        expr: Expr {
            expr_type: ast::Type::Arrow {
                from: Box::new(Type::Tuple(Tuple::Mult(vec![]))),
                to: Box::new(Type::Tuple(Tuple::Mult(vec![]))),
                effects: vec![Type::Nominal(Name::from("IO"))]
            },
            expr_value: Value::Function(Function(vec![Branch {
                pattern: Expr {
                    expr_type: Type::Tuple(Tuple::Mult(vec![])),
                    expr_value: Value::Tuple(Tuple::Mult(vec![])),
                },
                expression: Expr {
                    expr_type: Type::Tuple(Tuple::Mult(vec![])),
                    expr_value: Value::Block(vec![Stmt::Binding(Binding {
                        name: Name::from("x"),
                        expr: Expr {
                            expr_type: Type::Hole("_".into()),
                            expr_value: Value::Variable(Name::from("x")),
                        },
                    }),]),
                },
                effects: vec![],
            }]))
        }
    })]));
}
