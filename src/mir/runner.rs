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

// hax
#[derive(Copy, Clone, Debug)]
enum Frame {
  Current,
  Previous,
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

  fn get_binding(
    &mut self,
    (frame, ref_): (Frame, mir::Reference),
  ) -> (*mut u8, mir::Type<'ctx>) {
    let base = self.stack.as_mut_ptr();
    let len = self.stack.len(); // for assertions
    let frame = match frame {
      Frame::Current => {
        self.current_state()
      }
      Frame::Previous => {
        self.call_stack[self.call_stack.len() - 2]
      }
    };
    let offset = |off: usize| {
      assert!(off < len, "tried to index out of bounds");
      unsafe {
        base.offset(off as isize)
      }
    };
    match frame.func.bindings[ref_.0 as usize].kind {
      mir::BindingKind::Return => {
        let off = offset(frame.return_value);
        (off, frame.func.ret_ty)
      },
      mir::BindingKind::Param(i) => {
        let off = offset(
          frame.params_start
          + frame.func.params.offset_of(i) as usize
        );
        (off, frame.func.params.get(i))
      }
      mir::BindingKind::Local(i) => {
        let off = offset(
          frame.locals_start
          + frame.func.locals.offset_of(i) as usize
        );
        (off, frame.func.locals.get(i))
      }
    }
  }

  unsafe fn write(
    &mut self,
    dst: (Frame, mir::Reference),
    (src, src_ty): (*mut u8, mir::Type<'ctx>),
  ) {
    let (dst, dst_ty) = self.get_binding(dst);
    assert!(
      dst_ty.0 as *const _ == src_ty.0 as *const _,
      "dst: {}, src: {}", dst_ty.0, src_ty.0,
    );
    ::std::ptr::copy(src, dst, dst_ty.0.size() as usize);
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

    let mut tmp = [0u8; 4];
    tmp.copy_from_slice(&self.stack[..4]);

    self.pop_state();

    unsafe {
      ::std::mem::transmute::<[u8; 4], i32>(tmp)
    }
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
        let mir::Statement { lhs, ref rhs } = *stmt;
        match *rhs {
          mir::Value::Literal(ref lit) => {
            self.stmt_lit(lhs, lit)
          }
          mir::Value::Reference(rhs) => {
            self.stmt_ref(lhs, rhs);
          }
          mir::Value::Add(add_lhs, add_rhs) => {
            self.stmt_add(lhs, add_lhs, add_rhs);
          }
          mir::Value::Call {
            ref callee,
            ref args,
          } => {
            self.stmt_call(lhs, callee, args);
          }
        }
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

impl<'mir, 'ctx> Runner<'mir, 'ctx> {
  fn stmt_ref(
    &mut self,
    dst: mir::Reference,
    src: mir::Reference,
  ) {
    let src = self.get_binding((Frame::Current, src));
    unsafe {
      self.write((Frame::Current, dst), src);
    }
  }

  fn stmt_call(
    &mut self,
    dst: mir::Reference,
    callee: &mir::FunctionDecl,
    args: &[mir::Reference],
  ) {
    self.push_state(*callee);
    for (i, &arg) in args.iter().enumerate() {
      let arg = self.get_binding((Frame::Previous, arg));
      let parm = mir::Reference::param(i as u32);
      unsafe {
        self.write((Frame::Current, parm), arg);
      }
    }
    self.call();

    let src = self.get_binding(
      (Frame::Current, mir::Reference::ret()),
    );
    unsafe {
      self.write((Frame::Previous, dst), src);
    }
    self.pop_state();
  }

  fn stmt_lit(
    &mut self,
    dst: mir::Reference,
    src: &mir::Literal,
  ) {
    use std::mem::transmute;
    use mir::{BuiltinType, IntSize};

    let mut backing = [0u8; 8];
    let ty = match *src {
      mir::Literal::Int(i) => {
        let arr = unsafe { transmute::<i32, [u8; 4]>(i) };
        backing[..4].copy_from_slice(&arr);
        self.mir.get_builtin_type(
          BuiltinType::SInt(IntSize::I32),
        )
      }
      mir::Literal::Bool(b) => {
        backing[0] = b as u8;
        self.mir.get_builtin_type(BuiltinType::Bool)
      }
    };
    unsafe {
      self.write(
        (Frame::Current, dst),
        (backing.as_mut_ptr(), ty),
      );
    }
  }

  unsafe fn get_value<T>(src: (*mut u8, mir::Type)) -> T {
    assert!(
      src.1.size() as usize
      == ::std::mem::size_of::<T>()
    );
    let mut ret = ::std::mem::uninitialized();
    ::std::ptr::copy(
      src.0,
      (&mut ret) as *mut T as *mut u8,
      ::std::mem::size_of::<T>(),
    );
    ret
  }

  fn stmt_add(
    &mut self,
    dst: mir::Reference,
    lhs: mir::Reference,
    rhs: mir::Reference,
  ) {
    let lhs = self.get_binding((Frame::Current, lhs));
    let rhs = self.get_binding((Frame::Current, rhs));
    unsafe {
      let mut src = ::std::mem::transmute::<i32, [u8; 4]>(
        Self::get_value::<i32>(lhs) + Self::get_value::<i32>(rhs)
      );
      self.write(
        (Frame::Current, dst),
        (src.as_mut_ptr(), lhs.1),
      );
    }
  }
}
