use mir::{self, Mir};

pub struct Runner<'mir, 'ctx: 'mir> {
  mir: &'mir Mir<'ctx>,
  //stacks: Vec<Vec<u8>>,
}

impl<'mir, 'ctx> Runner<'mir, 'ctx> {
  pub fn new(mir: &'mir Mir<'ctx>) -> Self {
    Runner { mir }
  }

  pub fn call(&mut self, name: &str) -> i32 {
    let current_func =
      self.mir.funcs.get(name).expect("function not found");
    let mut ret_value = None::<i32>;

    let mut stack = current_func
      .locals
      .iter()
      .map(|_ty| None::<i32>)
      .collect::<Vec<_>>();

    let mut cur_blk = 0;

    loop {
      for stmt in &current_func.blks[cur_blk].stmts {
        let mir::Statement { ref lhs, ref rhs } = *stmt;
        let mir::Value::Literal(rhs) = *rhs;
        let mir::Reference(lhs) = *lhs;
        if lhs == 0 {
          ret_value = Some(rhs);
        } else {
          // currently, references point to the local that is
          // 1 behind them. this will change once we get
          // reference parameters
          stack[(lhs - 1) as usize] = Some(rhs);
        }
      }
      match current_func.blks[cur_blk].term {
        mir::Terminator::Goto(blk) => {
          cur_blk = blk.0 as usize;
        }
        mir::Terminator::Return => if let Some(v) = ret_value {
          return v;
        } else {
          panic!("typeck should have caught this");
        },
      }
    }
  }
}
