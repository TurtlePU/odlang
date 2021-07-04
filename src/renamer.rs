use std::collections::HashMap;

use crate::ast::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Token(pub String);

pub fn rename(program: Program<Option<Token>, Token>) -> Renamed {
    let mut renamer = Renamer::default();
    let dup_globals: Vec<_> = program
        .iter()
        .filter_map(|binding| renamer.push_global(binding.name.clone()))
        .collect();
    let (program, unknowns): (_, Vec<_>) = program
        .into_iter()
        .map(|binding| renamer.rename_global(binding))
        .unzip();
    Renamed {
        program,
        dup_globals,
        unknowns: unknowns.concat(),
    }
}

pub struct Renamed {
    pub program: Program<Name, Name>,
    pub dup_globals: Vec<(Token, Token)>,
    pub unknowns: Vec<Token>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Name {
    Given(Token, usize),
    Generated(usize),
}

#[derive(Default)]
struct Renamer {
    last: HashMap<String, (usize, Token)>,
    counter: usize,
}

type Res<T> = (T, Vec<Token>);

impl Renamer {
    fn push_global(&mut self, name: Token) -> Option<(Token, Token)> {
        self.last
            .insert(name.0.clone(), (0, name.clone()))
            .map(|(_, x)| (x, name))
    }

    fn rename_global(
        &mut self,
        binding: Binding<Option<Token>, Token>,
    ) -> Res<Binding<Name, Name>> {
        let Binding { name, value } = binding;
        let name = Name::Given(name, 0);
        let (value, errs) = match value {
            TLValue::Expr(expr) => self.rename_expr(expr),
            TLValue::Data(data) => self.rename_data(data),
        };
        (Binding { name, value }, errs)
    }

    fn rename_expr(
        &mut self,
        expr: ValExpr<Option<Token>, Token>,
    ) -> Res<TLValue<Name, Name>> {
        todo!()
    }

    fn rename_data(
        &mut self,
        data: PureFun<TLParam<Token>, Data<Option<Token>, Token>>,
    ) -> Res<TLValue<Name, Name>> {
        todo!()
    }
}
