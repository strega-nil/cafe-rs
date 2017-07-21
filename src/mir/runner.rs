use mir::{self, Mir};

pub struct Runner<'mir, 'ctx: 'mir> {
  mir: &'mir Mir<'ctx>,
  //stacks: Vec<Vec<u8>>,
}

impl<'mir, 'ctx> Runner<'mir, 'ctx> {
  pub fn new(mir: &'mir Mir<'ctx>) -> Self {
    Runner {
      mir,
    }
  }

  pub fn call(&mut self, name: &str) -> i32 {
    let current_func =
      self.mir.funcs.get(name).expect("function not found");
    let mut ret_value = None::<i32>;
    for stmt in &current_func.blks[0].stmts {
      match *stmt {
        mir::Statement::Assign { ref lhs, ref rhs } => {
          if let mir::Reference(0) = *lhs {
            let mir::Value::Literal(rhs) = *rhs; {
              ret_value = Some(rhs);
            }
          } else {
            panic!("blech: {:?}", lhs);
          }
        }
        mir::Statement::Return => {
          return ret_value.expect("no write to return pointer");
        }
      }
    }
    panic!("no return statement");
  }
}
