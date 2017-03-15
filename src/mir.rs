use std::collections::HashMap;
use std::fmt::{self, Display};

use parser::{self, Ast, Item};

#[derive(Debug)]
enum LValue {
  Temporary(usize),
  Return,
}

impl Display for LValue {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      LValue::Temporary(n) => write!(f, "tmp{} =", n),
      LValue::Return => write!(f, "return"),
    }
  }
}

#[derive(Debug)]
enum RValue {
  IntegerLiteral(u64),
}

impl Display for RValue {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      RValue::IntegerLiteral(n) => write!(f, "{}", n),
    }
  }
}

#[derive(Debug)]
struct Statement {
  lhs: LValue,
  rhs: RValue,
}

impl Display for Statement {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    write!(f, "{} {}", self.lhs, self.rhs)
  }
}

#[derive(Debug)]
struct Function {
  name: String,
  temporaries: usize, // will eventually be a Vec<Type>
  // will eventually be a Vec<Block> (which includes statements)
  stmts: Vec<Statement>,
}

impl Function {
  fn new(name: String, blk: parser::Block) -> Self {
    use parser::Statement as PS;
    use parser::Expression as PE;

    let mut temporaries = 0usize;
    let mut stmts = vec![];
    for stmt in blk.stmts {
      let (lhs, rhs);
      match stmt {
        PS::Expression(e) => {
          lhs = LValue::Temporary(temporaries);
          temporaries += 1;
          rhs = match e {
            PE::IntegerLiteral(n) => RValue::IntegerLiteral(n),
          };
        }
      };
      stmts.push(Statement { lhs, rhs });
    }

    if let Some(e) = blk.expr {
      let rhs = match e {
        PE::IntegerLiteral(n) => RValue::IntegerLiteral(n),
      };
      stmts.push(Statement { lhs: LValue::Return, rhs });
    }

    Function {
      name,
      temporaries,
      stmts,
    }
  }

  fn run(&self) -> u64 {
    let mut temporaries = vec![None; self.temporaries];
    for stmt in &self.stmts {
      match *stmt {
        Statement {
          lhs: LValue::Return,
          rhs: RValue::IntegerLiteral(ret)
        } => return ret,
        Statement {
          lhs: LValue::Temporary(tmp),
          rhs: RValue::IntegerLiteral(n),
        } => {
          temporaries[tmp] = Some(n);
        }
      }
    }

    panic!("No return statement found in function {}", self.name);
  }
}

impl Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    writeln!(f, "fn {}() : i64 {{", self.name)?;
    for n in 0..self.temporaries {
      writeln!(f, "  let tmp{};", n)?;
    }
    for stmt in &self.stmts {
      writeln!(f, "  {};", stmt)?;
    }
    write!(f, "}}")
  }
}

#[derive(Debug)]
pub struct Mir {
  functions: HashMap<String, Function>,
}

impl Display for Mir {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    for func in &self.functions {
      writeln!(f, "{}", func.1)?;
    }
    Ok(())
  }
}

impl Mir {
  pub fn lower(ast: Ast) -> Self {
    let mut functions = HashMap::new();
    for item in ast.items {
      match item {
        Item::Function {
          name,
          blk,
        } => {
          functions.insert(name.clone(), Function::new(name, blk));
        }
      }
    }

    Mir {
      functions
    }
  }

  pub fn run(&self, name: &str) -> Option<u64> {
    self.functions.get(name).map(Function::run)
  }
}
