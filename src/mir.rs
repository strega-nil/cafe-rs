use ast::Ast;
use std::collections::HashMap;

struct Function;
struct Type;

pub struct Mir {
  functions: Vec<Function>,
  types: HashMap<String, Type>,
}

impl Mir {
  pub fn new(ast: Ast) -> Self {
    let _ast = ast;
    let _self = Mir {
      functions: vec![],
      types: HashMap::new(),
    };
    // build mir
    _self
  }

  pub fn print(&self) {
    unimplemented!()
  }

  pub fn run(&self) {
    unimplemented!()
  }
}
