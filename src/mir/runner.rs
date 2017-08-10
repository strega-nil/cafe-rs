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
    struct FunctionState<'a, 'b: 'a> {
      current_func: &'a mir::FunctionValue<'b>,
      ret_value: Option<i32>,
      params: Vec<i32>,
      stack: Vec<Option<i32>>,
    }
    impl<'a, 'b: 'a> FunctionState<'a, 'b> {
      fn read_binding(&self, ref_: mir::Reference) -> i32 {
        match self.current_func.bindings[ref_.0 as usize].kind {
          mir::BindingKind::Return => {
            panic!("attempted to read return binding");
          }
          mir::BindingKind::Param(i) => {
            self.params[i as usize]
          }
          mir::BindingKind::Local(i) => {
            self.stack[i as usize].expect(
              "Attempt to read a binding which hasn't been written to",
            )
          }
        }
      }
      fn write_binding(&mut self, ref_: mir::Reference, val: i32) {
        match self.current_func.bindings[ref_.0 as usize].kind {
          mir::BindingKind::Return => {
            self.ret_value = Some(val);
          }
          mir::BindingKind::Param(i) => {
            self.params[i as usize] = val;
          }
          mir::BindingKind::Local(i) => {
            self.stack[i as usize] = Some(val);
          }
        }
      }
    }

    let current_func = match self.mir.funcs[func.0].1 {
      Some(ref f) => { f }
      None => {
        panic!(
          "Function never defined: {:?} ({:?})",
          self.mir.funcs[func.0].0,
          func,
        );
      }
    };
    assert!(params.len() == current_func.params.len());

    let mut state = FunctionState {
      current_func,
      ret_value: None,
      params: params.to_owned(),
      stack: vec![None; current_func.locals.len()],
    };

    let mut cur_blk = 0;

    loop {
      for stmt in &current_func.blks[cur_blk].stmts {
        let mir::Statement { ref lhs, ref rhs } = *stmt;
        let rhs = match *rhs {
          mir::Value::Literal(lit) => { lit }
          mir::Value::Reference(ref_) => {
            state.read_binding(ref_)
          }
          mir::Value::Add(lhs, rhs) => {
            let lhs = state.read_binding(lhs);
            let rhs = state.read_binding(rhs);
            lhs + rhs
          }
          mir::Value::Call { ref callee, ref args } => {
            let args: Vec<_> =
              args
                .iter()
                .map(|&r| state.read_binding(r))
                .collect();
            self.call(*callee, &args)
          }
        };
        state.write_binding(*lhs, rhs);
      }
      match current_func.blks[cur_blk].term {
        mir::Terminator::Goto(blk) => {
          cur_blk = blk.0 as usize;
        }
        mir::Terminator::Return => {
          if let Some(v) = state.ret_value {
            return v;
          } else {
            panic!("typeck should have caught this");
          }
        }
      }
    }
  }
}
