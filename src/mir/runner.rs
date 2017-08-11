use mir::{self, align, Mir};

const UNINITIALIZED: u8 = 0x42;

// meant to be the state of a single function
#[derive(Copy, Clone, Debug)]
struct FunctionState<'mir, 'ctx: 'mir> {
  func: &'mir mir::FunctionValue<'ctx>,
  // indices into the stack
  // NOTE(ubsan): more information is held than actually
  // necessary
  // technically, we only need to keep `return_value` and can
  // calculate the rest
  return_value: usize,
  params_start: usize,
  locals_start: usize,
}

pub struct Runner<'mir, 'ctx: 'mir> {
  mir: &'mir Mir<'ctx>,
  call_stack: Vec<FunctionState<'mir, 'ctx>>,
  stack: Vec<u8>,
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

  unsafe fn read<T: Copy>(&self, idx: usize) -> T {
    let ptr = &self.stack[idx];
    *(ptr as *const _ as *const T)
  }

  unsafe fn write<T: Copy>(&mut self, idx: usize, t: T) {
    let ptr = &mut self.stack[idx];
    *(ptr as *mut _ as *mut T) = t;
  }

  // for function calls
  // reads from the previous stack frame
  fn read_ref_prev(&self, ref_: mir::Reference) -> i32 {
    let cur = self.call_stack[self.call_stack.len() - 2];
    match cur.func.bindings[ref_.0 as usize].kind {
      mir::BindingKind::Return => unsafe {
        self.read::<i32>(cur.return_value)
      },
      mir::BindingKind::Param(i) => {
        let offset = cur.func.params.offset_of(i) as usize;
        unsafe { self.read::<i32>(cur.params_start + offset) }
      }
      mir::BindingKind::Local(i) => {
        let offset = cur.func.locals.offset_of(i) as usize;
        unsafe { self.read::<i32>(cur.locals_start + offset) }
      }
    }
  }

  fn read_ref(&self, ref_: mir::Reference) -> i32 {
    let cur = self.current_state();
    match cur.func.bindings[ref_.0 as usize].kind {
      mir::BindingKind::Return => unsafe {
        self.read::<i32>(cur.return_value)
      },
      mir::BindingKind::Param(i) => {
        let offset = cur.func.params.offset_of(i) as usize;
        unsafe { self.read::<i32>(cur.params_start + offset) }
      }
      mir::BindingKind::Local(i) => {
        let offset = cur.func.locals.offset_of(i) as usize;
        unsafe { self.read::<i32>(cur.locals_start + offset) }
      }
    }
  }

  fn write_ref(&mut self, ref_: mir::Reference, val: i32) {
    let cur = self.current_state();
    let binding = &cur.func.bindings[ref_.0 as usize];
    match binding.kind {
      mir::BindingKind::Return => unsafe {
        self.write(cur.return_value, val);
      },
      mir::BindingKind::Param(i) => {
        let offset = cur.func.params.offset_of(i) as usize;
        unsafe {
          self.write(cur.params_start + offset, val);
        }
      }
      mir::BindingKind::Local(i) => {
        let offset = cur.func.locals.offset_of(i) as usize;
        unsafe {
          self.write(cur.locals_start + offset, val);
        }
      }
    }
  }

  fn pop_state(&mut self) {
    let new_size = self.current_state().return_value;
    self.stack.resize(new_size, UNINITIALIZED);
    self.call_stack.pop();
  }

  // after this call, the stack will be set up for the call,
  // but without arguments
  fn push_state(&mut self, func: mir::FunctionDecl) {
    let func = match self.mir.funcs[func.0].1 {
      Some(ref f) => f,
      None => {
        panic!(
          "Function never defined: {:?} ({:?})",
          self.mir.funcs[func.0].0,
          func,
        );
      }
    };
    let return_value =
      align(self.stack.len(), func.ret_ty.align() as usize);
    let return_end = return_value + func.ret_ty.size() as usize;
    let params_start = align(return_end, 16);
    let locals_start =
      params_start + func.params.size() as usize;

    self.stack.resize(locals_start, UNINITIALIZED);

    self.call_stack.push(FunctionState {
      func,
      return_value,
      params_start,
      locals_start,
    });
  }

  pub fn run(&mut self, func: mir::FunctionDecl) -> i32 {
    self.push_state(func);
    self.call();
    let tmp = self.read_ref(mir::Reference::ret());
    self.pop_state();
    tmp
  }

  fn call(&mut self) {
    {
      let loc_size = self.current_state().func.locals.size();
      let new_size = self.stack.len() + loc_size as usize;
      self.stack.resize(new_size, UNINITIALIZED);
    }
    let mut cur_blk = 0;

    loop {
      for stmt in
        &self.current_state().func.blks[cur_blk].stmts
      {
        let mir::Statement { ref lhs, ref rhs } = *stmt;
        let rhs = match *rhs {
          mir::Value::Literal(lit) => lit,
          mir::Value::Reference(ref_) => self.read_ref(ref_),
          mir::Value::Add(lhs, rhs) => {
            let lhs = self.read_ref(lhs);
            let rhs = self.read_ref(rhs);
            lhs + rhs
          }
          mir::Value::Call {
            ref callee,
            ref args,
          } => {
            self.push_state(*callee);
            for (i, r) in args.iter().enumerate() {
              let i = i as u32;
              let tmp = self.read_ref_prev(*r);
              self.write_ref(mir::Reference::param(i), tmp);
            }
            self.call();
            let tmp = self.read_ref(mir::Reference::ret());
            self.pop_state();
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
          return;
        }
      }
    }
  }
}
