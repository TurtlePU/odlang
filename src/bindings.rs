use std::{collections::HashMap, hash::Hash};

use crate::ast::{
    Binding, Body, Branch, Call, CompTime, Decl, Expr, Function, Name, Program,
    Stmt, Tuple, Type, Value,
};

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Key<'a>(pub Scope<'a>, pub Name);

#[derive(Debug, Default)]
pub struct Bindings<'a> {
    values: HashMap<Key<'a>, BoundTo<'a>>,
    types: HashMap<Name, &'a Body>,
}

#[derive(Debug)]
pub enum BoundTo<'a> {
    Expr(&'a Expr),
    Pattern(&'a Type),
}

#[derive(Clone, Copy, Debug)]
pub enum Scope<'a> {
    TopLevel,
    Inside(&'a Function),
}

impl<'a> PartialEq for Scope<'a> {
    fn eq(&self, rhs: &Scope<'a>) -> bool {
        use Scope::*;
        match (self, rhs) {
            (TopLevel, TopLevel) => true,
            (Inside(ptr), Inside(qtr)) => ptr as *const _ == qtr,
            _ => false,
        }
    }
}

impl<'a> Eq for Scope<'a> {}

impl<'a> Hash for Scope<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::TopLevel => 0_usize.hash(state),
            Self::Inside(ptr) => (*ptr as *const _ as usize).hash(state),
        }
    }
}

impl<'a> From<&'a Program> for Bindings<'a> {
    fn from(program: &'a Program) -> Self {
        use Decl::*;
        program.iter().fold(Default::default(), |b, d| match d {
            TopLevelValue(expr) => b.visit_binding(Scope::TopLevel, expr),
            CompTime(comptime) => b.visit_comp(comptime),
        })
    }
}

impl<'a> Bindings<'a> {
    fn visit_binding(mut self, scope: Scope<'a>, binding: &'a Binding) -> Self {
        let Binding { name, expr } = binding;
        self.values
            .insert(Key(Scope::TopLevel, name.clone()), BoundTo::Expr(expr));
        self.visit_expression(scope, expr)
    }

    fn visit_pattern(mut self, scope: Scope<'a>, pattern: &'a Expr) -> Self {
        let Expr {
            expr_type,
            expr_value,
        } = pattern;
        use self::Tuple::*;
        use Value::*;
        match expr_value {
            Variable(name) => {
                self.values.insert(
                    Key(scope, name.clone()),
                    BoundTo::Pattern(expr_type),
                );
                self
            }
            Tuple(tuple) => match tuple {
                Add(vars) | Mult(vars) => vars
                    .iter()
                    .fold(self, |bind, var| bind.visit_pattern(scope, var)),
            },
            Call(call) => call
                .args
                .iter()
                .fold(self, |bind, arg| bind.visit_pattern(scope, arg)),
            _ => unreachable!(),
        }
    }

    fn visit_expression(self, scope: Scope<'a>, expr: &'a Expr) -> Self {
        use Value::*;
        match &expr.expr_value {
            Variable(_) => self,
            Tuple(_) => self,
            Function(ref f) => f.0.iter().fold(self, |bind, branch| {
                let Branch {
                    pattern,
                    expression,
                    effects: _,
                } = branch;
                bind.visit_pattern(Scope::Inside(f), pattern)
                    .visit_expression(Scope::Inside(f), expression)
            }),
            Call(call) => {
                let self::Call { function, args } = call;
                args.iter().fold(
                    self.visit_expression(scope, function),
                    |bind, expr| bind.visit_expression(scope, expr),
                )
            }
            Block(stmts) => stmts.iter().fold(self, |bind, stmt| match stmt {
                Stmt::Expression(expr) => bind.visit_expression(scope, expr),
                Stmt::Binding(binding) => bind.visit_binding(scope, binding),
            }),
        }
    }

    fn visit_comp(mut self, comptime: &'a CompTime) -> Self {
        let CompTime {
            name,
            typevars: _,
            body,
        } = comptime;
        self.types.insert(name.clone(), body);
        self
    }
}
