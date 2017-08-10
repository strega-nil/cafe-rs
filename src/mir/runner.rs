use mir::{self, Mir};

pub struct Runner<'mir, 'ctx: 'mir> {
  mir: &'mir Mir<'ctx>,
  //stacks: Vec<Vec<u8>>,
}

impl<'mir, 'ctx> Runner<'mir, 'ctx> {
  pub fn new(mir: &'mir Mir<'ctx>) -> Self {
    Runner { mir }
  }

  pub fn call(
    &mut self,
    func: mir::FunctionDecl,
    params: &[i32],
  ) -> i32 {
    let current_func = match self.mir.funcs[func.0].1 {
      Some(ref f) => {
        f
      }
      None => {
        panic!(
          "Function never defined: {:?} ({:?})",
          self.mir.funcs[func.0].0,
          func,
        );
      }
    };
    assert!(params.len() == current_func.params.len());
    let mut ret_value = None::<i32>;

    let mut stack = current_func
      .locals
      .iter()
      .map(|_ty| None::<i32>)
      .collect::<Vec<_>>();

    let mut cur_blk = 0;

    fn read_binding(
      bindings: &[mir::Binding],
      params: &[i32],
      locals: &[Option<i32>],
      ref_: mir::Reference,
    ) -> i32 {
      match bindings[ref_.0 as usize].kind {
        mir::BindingKind::Return => {
          panic!("attempted to read return binding");
        }
        mir::BindingKind::Param(i) => {
          params[i as usize]
        }
        mir::BindingKind::Local(i) => {
          locals[i as usize].expect(
            "Attempt to read a binding which hasn't been written to",
          )
        }
      }
    }

    fn to_value(v: &mir::Value) -> i32 {
      match *v {
        mir::Value::Literal(lit) => { lit }
        mir::Value::Reference(ref_) => {
          read_binding(
            &current_func.bindings,
            &params,
            &stack,
            ref_,
          )
        }
        mir::Value::Add(lhs, rhs) => {
          let lhs = read_binding(
            &current_func.bindings,
            &params,
            &stack,
            lhs,
          );
          let rhs = read_binding(
            &current_func.bindings,
            &params,
            &stack,
            rhs,
          );
          lhs + rhs
        }
        mir::Value::Call { ref callee, ref args } => {
          let args: Vec<_> =
            args
              .iter()
              .map(|r| to_value(v))
              .collect();
          self.call(*callee, &args)
        }
      }
    }

    loop {
      for stmt in &current_func.blks[cur_blk].stmts {
        let mir::Statement { ref lhs, ref rhs } = *stmt;
        let rhs = to_value(rhs);
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
