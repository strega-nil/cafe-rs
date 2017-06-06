use ast::Ast;

pub struct Mir {
  ast: Ast,
}

impl Mir {
  pub fn new(ast: Ast) -> Self {
    Mir {
      ast
    }
  }

  pub fn print(&self) {
    unimplemented!()
  }

  pub fn run(&self) {
    unimplemented!()
  }
}
