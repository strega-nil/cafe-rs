use mir::{self, Mir};

use ty::{self, Type, TypeVariant};

// TODO(ubsan): represent uninit data
#[derive(Clone, Debug)]
pub enum Value {
  S8(i8),
  S16(i16),
  S32(i32),
  S64(i64),
  U8(u8),
  U16(u16),
  U32(u32),
  U64(u64),
  Bool(bool),
  Unit,
}

impl Value {
  fn is_same_kind(&self, other: &Self) -> bool {
    use self::Value::*;
    match (self, other) {
      (&S8(_), &S8(_)) => true,
      (&S16(_), &S16(_)) => true,
      (&S32(_), &S32(_)) => true,
      (&S64(_), &S64(_)) => true,
      (&U8(_), &U8(_)) => true,
      (&U16(_), &U16(_)) => true,
      (&U32(_), &U32(_)) => true,
      (&U64(_), &U64(_)) => true,
      (&Bool(_), &Bool(_)) => true,
      (&Unit, &Unit) => true,
      _ => false,
    }
  }
}

fn ty_to_default_value(ty: &Type) -> Value {
  match *ty.0 {
    TypeVariant::SInt(ty::Int::I8) => Value::S8(0),
    TypeVariant::SInt(ty::Int::I16) => Value::S16(0),
    TypeVariant::SInt(ty::Int::I32) => Value::S32(0),
    TypeVariant::SInt(ty::Int::I64) => Value::S64(0),
    TypeVariant::UInt(ty::Int::I8) => Value::U8(0),
    TypeVariant::UInt(ty::Int::I16) => Value::U16(0),
    TypeVariant::UInt(ty::Int::I32) => Value::U32(0),
    TypeVariant::UInt(ty::Int::I64) => Value::U64(0),
    TypeVariant::Bool => Value::Bool(false),
    TypeVariant::Unit => Value::Unit,
    TypeVariant::Reference(_) => panic!("references not implemented"),
    TypeVariant::Diverging
    | TypeVariant::Infer(_)
    | TypeVariant::InferInt(_)
    => unreachable!(),
  }
}

impl mir::Literal {
  fn to_interp_value(&self) -> Value {
    use mir::Literal::*;
    match *self {
      Unit => Value::Unit,
      Bool(b) => Value::Bool(b),
      Int { value, signed: true, ty: ty::Int::I8 } => Value::S8(value as _),
      Int { value, signed: true, ty: ty::Int::I16 } => Value::S16(value as _),
      Int { value, signed: true, ty: ty::Int::I32 } => Value::S32(value as _),
      Int { value, signed: true, ty: ty::Int::I64 } => Value::S64(value as _),
      Int { value, signed: false, ty: ty::Int::I8 } => Value::U8(value as _),
      Int { value, signed: false, ty: ty::Int::I16 } => Value::U16(value as _),
      Int { value, signed: false, ty: ty::Int::I32 } => Value::U32(value as _),
      Int { value, signed: false, ty: ty::Int::I64 } => Value::U64(value as _),
    }
  }
}

impl mir::Value {
  fn to_interp_value(&self, runner: &FunctionRun) -> Value {
    use mir::ValueKind as Vk;
    use mir::{Local, Parameter};
    match self.0 {
      Vk::Literal(ref lit) => {
        lit.to_interp_value()
      },
      Vk::Local(Local(n)) => {
        runner.locals[n as usize].clone()
      },
      Vk::Parameter(Parameter(n)) => {
        runner.params[n as usize].clone()
      },
      Vk::Call {
        ref callee,
        ref args,
      } => {
        let args = args
          .iter()
          .map(|&Local(n)| runner.locals[n as usize].clone())
          .collect();
        FunctionRun::new(runner.mir, callee, args).run()
      },
      Vk::Lte(Local(lhs), Local(rhs)) => {
        runner.locals[lhs as usize] <= runner.locals[rhs as usize]
      },
      ref vk => panic!("not yet implemented: {:?}", vk),
    }
  }
}

struct FunctionRun<'a, 't> where 't: 'a {
  mir: &'a Mir<'t>,
  func: &'a mir::Function<'t>,
  ret: Value,
  locals: Vec<Value>,
  params: Vec<Value>,
  current_block: &'a mir::BlockData,
}

impl<'a, 't> FunctionRun<'a, 't> {
  fn new(mir: &'a Mir<'t>, name: &str, params: Vec<Value>) -> Self {
    let func = mir.functions.get(name).expect("Non-existent function");
    let ret = ty_to_default_value(&func.ty.output());
    let locals = value_vec(&func.locals);
    let current_block = &func.blocks[0];
    FunctionRun {
      mir,
      func,
      ret,
      locals,
      params,
      current_block,
    }
  }

  fn run(mut self) -> Value {
    use mir::Terminator as Term;
    loop {
      for inst in &self.current_block.statements {
        let lvalue = &inst.0;
        let rvalue = &inst.1;

        self.write(lvalue, rvalue);
      }

      let new_blk = match self.current_block.terminator {
        Term::Return => return self.ret,
        Term::Goto(mir::Block(n)) => &self.func.blocks[n],
        _ => unimplemented!(),
      };
      self.current_block = new_blk;
    }
  }

  fn write(
    &mut self,
    lhs: &mir::Lvalue,
    rhs: &mir::Value,
  ) {
    use mir::Lvalue as Lv;

    let rhs = rhs.to_interp_value(&self);
    let lhs = match *lhs {
      Lv::Local(mir::Local(n)) => &mut self.locals[n as usize],
      Lv::Return => &mut self.ret,
      Lv::Deref(_) => unimplemented!(),
    };
    assert!(lhs.is_same_kind(&rhs));
    *lhs = rhs;
  }
}

fn value_vec(tys: &Vec<Type>) -> Vec<Value> {
  tys.iter().map(ty_to_default_value).collect()
}

impl<'t> Mir<'t> {
  pub fn run_function(&self, name: &str, params: Vec<Value>) -> Value {
    let run = FunctionRun::new(self, name, params);
    run.run()
  }
}
