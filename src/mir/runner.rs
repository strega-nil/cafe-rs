use mir::{self, Mir};

const UNINITIALIZED: i32 = 0x42424242;

// meant to be the state of a single function
#[derive(Copy, Clone)]
struct FunctionState<'mir, 'ctx: 'mir> {
  func: &'mir mir::FunctionValue<'ctx>,
  // indices into the stack
  // NOTE(ubsan): more information is held than actually
  // necessary
  // technically, we only need to keep `return_value` and can
  // calculate the rest
  return_value: usize,
  locals_start: usize,
}

pub struct Runner<'mir, 'ctx: 'mir> {
  mir: &'mir Mir<'ctx>,
  call_stack: Vec<FunctionState<'mir, 'ctx>>,
  stack: Vec<i32>,
}

impl<'mir, 'ctx> Runner<'mir, 'ctx> {
  pub fn new(mir: &'mir Mir<'ctx>) -> Self {
    Runner {
      mir,
      call_stack: vec![],
      stack: vec![],
    }
  }

  fn current_state(&self) -> FunctionState<'mir, 'ctx> {
    *self.call_stack.last().expect("nothing on the call stack")
  }

  fn read_ref(&self, ref_: mir::Reference) -> i32 {
    let cur = self.current_state();
    match cur.func.bindings[ref_.0 as usize].kind {
      mir::BindingKind::Return => {
        // this is technically valid, but something I do want to
        // catch
        // because I think it means a bug in the compiler
        panic!("attempted to read return binding");
      }
      mir::BindingKind::Param(i) => {
        self.stack[cur.return_value + 1 + (i as usize)]
      }
      mir::BindingKind::Local(i) => {
        self.stack[cur.locals_start + (i as usize)]
      }
    }
  }

  fn write_ref(&mut self, ref_: mir::Reference, val: i32) {
    let cur = self.current_state();
    match cur.func.bindings[ref_.0 as usize].kind {
      mir::BindingKind::Return => {
        self.stack[cur.return_value] = val;
      }
      mir::BindingKind::Param(i) => {
        self.stack[cur.return_value + 1 + (i as usize)] = val;
      }
      mir::BindingKind::Local(i) => {
        self.stack[cur.locals_start + (i as usize)] = val;
      }
    }
  }

  fn pop_state(&mut self) {
    self.call_stack.pop();
  }

  fn push_state(
    &mut self,
    func: mir::FunctionDecl,
    return_value: usize,
  ) {
    let func = match self.mir.funcs[func.0].1 {
      Some(ref f) => { f }
      None => {
        panic!(
          "Function never defined: {:?} ({:?})",
          self.mir.funcs[func.0].0,
          func,
        );
      }
    };
    let locals_start = return_value + 1 + func.params.len();

    assert!(
      self.stack.len() == locals_start,
      "either too many or too few parameters on the stack"
    );

    self.call_stack.push(FunctionState {
      func,
      return_value,
      locals_start,
    });
  }

  pub fn run(&mut self, func: mir::FunctionDecl) -> i32 {
    self.stack.resize(1, UNINITIALIZED);
    self.push_state(func, 0);
    self.call();
    return self.stack[0];
  }

  fn call(&mut self) {
    {
      let loc_len = self.current_state().func.locals.len();
      let new_size = self.stack.len() + loc_len;
      self.stack.resize(new_size, UNINITIALIZED);
    }
    let mut cur_blk = 0;

    loop {
      for stmt in
        &self.current_state().func.blks[cur_blk].stmts
      {
        let mir::Statement { ref lhs, ref rhs } = *stmt;
        let rhs = match *rhs {
          mir::Value::Literal(lit) => { lit }
          mir::Value::Reference(ref_) => {
            self.read_ref(ref_)
          }
          mir::Value::Add(lhs, rhs) => {
            let lhs = self.read_ref(lhs);
            let rhs = self.read_ref(rhs);
            lhs + rhs
          }
          mir::Value::Call { ref callee, ref args } => {
            let return_value = self.stack.len();
            self.stack.resize(
              return_value + args.len() + 1,
              UNINITIALIZED,
            );
            for (i, r) in args.iter().enumerate() {
              let tmp = self.read_ref(*r);
              self.stack[return_value + 1 + i] = tmp;
            }
            self.push_state(*callee, return_value);
            self.call();
            let tmp = self.stack[return_value];
            self.stack.resize(return_value, UNINITIALIZED);
            tmp
          }
        };
        self.write_ref(*lhs, rhs);
      }
      match self.current_state().func.blks[cur_blk].term {
        mir::Terminator::Goto(blk) => {
          cur_blk = blk.0 as usize;
        }
        mir::Terminator::Return => {
          self.pop_state();
          return;
        }
      }
    }
  }
}
