use std;
use std::collections::HashMap;
use ty::{self, Type, TypeVariant, TypeContext};

mod llvm;
mod fmt;

const START_BLOCK: Block = Block(0);
const END_BLOCK: Block = Block(1);

#[derive(Debug)]
pub struct Function<'t> {
  ty: ty::Function<'t>,
  temporaries: Vec<Type<'t>>,
  locals: Vec<Type<'t>>,
  blocks: Vec<BlockData>,
}
#[derive(Copy, Clone, Debug)]
pub struct Local(u32);
#[derive(Copy, Clone, Debug)]
struct Parameter(u32);

impl<'t> Function<'t> {
  pub fn new(ty: ty::Function<'t>) -> Self {
    let mut ret = Function {
      ty: ty,
      temporaries: Vec::new(),
      locals: Vec::new(),
      blocks: Vec::new(),
    };
    assert_eq!(
      START_BLOCK, ret.new_block(Lvalue::Return, Terminator::Goto(END_BLOCK))
    );
    assert_eq!(END_BLOCK, ret.new_block(Lvalue::Return, Terminator::Return));
    let input_types = ret.ty.input().to_owned();
    {
      for ty in &input_types {
        ret.new_local(*ty);
      }
      let blk = ret.get_block(&mut START_BLOCK);
      for i in 0..input_types.len() as u32 {
        blk.statements.push(Statement(
          Lvalue::Local(Local(i)), Value(ValueKind::Parameter(Parameter(i)))
        ))
      }
    }
    END_BLOCK.terminate(&mut ret, Terminator::Return);
    ret
  }

  pub fn start_block(&self) -> Block {
    START_BLOCK
  }

  fn new_block(&mut self, expr: Lvalue, term: Terminator) -> Block {
    self.blocks.push(BlockData::new(expr, term));
    Block(self.blocks.len() - 1)
  }
  pub fn new_local(&mut self, ty: Type<'t>) -> Local {
    assert!(self.locals.len() < u32::max_value() as usize);
    self.locals.push(ty);
    Local(self.locals.len() as u32 - 1)
  }
  pub fn get_param_local(&mut self, n: u32) -> Local {
    assert!(n < self.ty.input().len() as u32);
    Local(n)
  }

  fn get_block(&mut self, blk: &mut Block) -> &mut BlockData {
    &mut self.blocks[blk.0 as usize]
  }
  fn get_param_ty(&self, par: Parameter) -> Type<'t> {
    self.ty.input()[par.0 as usize]
  }
  fn get_local_ty(&self, var: Local) -> Type<'t> {
    self.locals[var.0 as usize]
  }

  fn flatten(
    &mut self,
    value: Value,
    mir: &Mir<'t>,
    block: &mut Block,
    fn_types: &HashMap<String,
    ty::Function<'t>>,
  ) -> Local {
    if let ValueKind::Lvalue(Lvalue::Local(local)) = value.0 {
      local
    } else {
      let ty = value.ty(mir, self, fn_types);
      let loc = self.new_local(ty);
      block.add_stmt(Lvalue::Local(loc), value, self);
      loc
    }
  }

  fn build(
    self,
    mir: &Mir<'t>,
    llfunc: llvm::Value,
    funcs: &HashMap<String, (llvm::Value, Type<'t>)>,
  ) {
    LlFunction::build(mir, self, llfunc, funcs)
  }
}

pub struct LlFunction<'t> {
  mir: Function<'t>,
  raw: llvm::Value,
  builder: llvm::Builder,
  ret_ptr: llvm::Value,
  locals: Vec<llvm::Value>,
  blocks: Vec<llvm::BasicBlock>,
}

impl<'t> LlFunction<'t> {
  fn build(
    mir: &Mir<'t>,
    mirfunc: Function<'t>,
    llfunc: llvm::Value,
    funcs: &HashMap<String, (llvm::Value, Type<'t>)>,
  ) {
    let builder = llvm::Builder::new();
    let mut blocks = Vec::new();
    for i in 0..mirfunc.blocks.len() {
      blocks.push(llvm::BasicBlock::append(llfunc, i as u32));
    }

    builder.position_at_end(blocks[0]);

    let mut locals = Vec::new();
    for mir_local in &mirfunc.locals {
      locals.push(builder.build_alloca(
        llvm::get_type(&mir.target_data, *mir_local), "var"
      ));
    }

    let ret_ptr = builder.build_alloca(
      llvm::get_type(&mir.target_data, mirfunc.ty.output()), "ret",
    );

    let mut self_ = LlFunction {
      mir: mirfunc,
      raw: llfunc,
      builder: builder,
      ret_ptr: ret_ptr,
      locals: locals,
      blocks: blocks,
    };

    let mut i = self_.mir.blocks.len();
    while let Some(blk) = self_.mir.blocks.pop() {
      i -= 1;
      self_.builder.position_at_end(self_.blocks[i]);
      for stmt in blk.statements {
        stmt.to_llvm(mir, &mut self_, funcs);
      }
      blk.terminator.to_llvm(mir, &self_);
    }
  }


  fn get_local_ptr(&self, var: Local) -> llvm::Value {
    self.locals[var.0 as usize]
  }
  fn get_local_value(&self, var: Local) -> llvm::Value {
    self.builder.build_load(self.locals[var.0 as usize])
  }

  fn get_block(&self, blk: &Block) -> llvm::BasicBlock {
    self.blocks[blk.0]
  }
}

// TODO(ubsan): get rid of Clone, switch to Clone and CloneData implementation
#[derive(Clone, Debug)]
enum Literal {
  Int {
    value: u64,
    signed: bool,
    ty: ty::Int,
  },
  Bool(bool),
  Tuple(Vec<Local>),
}

impl Literal {
  fn llvm_store<'t>(
    self,
    dst: llvm::Value,
    function: &LlFunction<'t>
  ) {
    match self {
      Literal::Int {
        value,
        ty,
        ..
      } => {
        function.builder.build_store(
          dst,
          llvm::Value::const_int(llvm::get_int_type(ty), value),
        )
      }
      Literal::Bool(value) => {
        function.builder.build_store(
          dst,
          llvm::Value::const_bool(value),
        )
      }
      Literal::Tuple(v) => {
        let mut llvm_v = Vec::new();
        for el in v {
          llvm_v.push(function.get_local_value(el));
        }
        llvm::Value::make_struct(dst, &function.builder, &llvm_v)
      }
    }
  }

  fn ty<'t>(&self, mir: &Mir<'t>, function: &Function<'t>) -> Type<'t> {
    match *self {
      Literal::Int {
        ty,
        ..
      } => Type::sint(ty, mir.ctxt),
      Literal::Bool(_) => Type::bool(mir.ctxt),
      Literal::Tuple(ref v) => {
        let mut type_v = Vec::new();
        for el in v {
          type_v.push(function.get_local_ty(*el));
        }
        Type::tuple(type_v, mir.ctxt)
      }
    }
  }
}

#[derive(Clone, Debug)]
enum ValueKind {
  Literal(Literal),
  Parameter(Parameter),
  Lvalue(Lvalue),

  // -- unops --
  Pos(Local),
  Neg(Local),
  Not(Local),

  Ref(Local),

  // -- binops --
  Add(Local, Local),
  Sub(Local, Local),
  Mul(Local, Local),
  Div(Local, Local),
  Rem(Local, Local),
  And(Local, Local),
  Xor(Local, Local),
  Or(Local, Local),
  Shl(Local, Local),
  Shr(Local, Local),

  // -- comparison --
  Eq(Local, Local),
  Neq(Local, Local),
  Lt(Local, Local),
  Lte(Local, Local),
  Gt(Local, Local),
  Gte(Local, Local),

  // -- other --
  Call {
    callee: String,
    args: Vec<Local>,
  },
}

#[derive(Debug)]
pub struct Value(ValueKind);

// --- CONSTRUCTORS ---
impl Value {
  // -- leaves --
  #[inline(always)]
  pub fn int_literal(value: u64, ty: ty::Int, signed: bool) -> Self {
    Value(ValueKind::Literal(
      Literal::Int {
        value: value,
        signed: signed,
        ty: ty,
      }
    ))
  }
  #[inline(always)]
  pub fn bool_literal(value: bool) -> Self {
    Value(ValueKind::Literal(Literal::Bool(value)))
  }
  pub fn tuple_literal<'t>(
    v: Vec<Value>,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>
  ) -> Value {
    let mut leaf_v = Vec::new();
    for el in v {
      leaf_v.push(function.flatten(el, mir, block, fn_types))
    }
    Value(ValueKind::Literal(Literal::Tuple(leaf_v)))
  }
  #[inline(always)]
  pub fn unit_literal() -> Value {
    Value(ValueKind::Literal(Literal::Tuple(vec![])))
  }

  #[inline(always)]
  pub fn param(arg_num: u32, function: &mut Function) -> Self {
    assert!(arg_num < function.ty.input().len() as u32);
    Value::local(function.get_param_local(arg_num))
  }
  #[inline(always)]
  pub fn local(local: Local) -> Self {
    Value::lvalue(Lvalue::Local(local))
  }
  #[inline(always)]
  fn lvalue(lvalue: Lvalue) -> Self {
    Value(ValueKind::Lvalue(lvalue))
  }

  // -- unops --
  pub fn pos<'t>(
    inner: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Pos(function.flatten(inner, mir, block, fn_types)))
  }
  pub fn neg<'t>(
    inner: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Neg(function.flatten(inner, mir, block, fn_types)))
  }
  pub fn not<'t>(
    inner: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Not(function.flatten(inner, mir, block, fn_types)))
  }
  pub fn ref_<'t>(
    inner: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    let inner_ty = inner.ty(mir, function, fn_types);
    let inner = function.flatten(inner, mir, block, fn_types);
    let ptr = function.new_local(Type::ref_(inner_ty, mir.ctxt));
    block.add_stmt(Lvalue::Local(ptr), Value(ValueKind::Ref(inner)), function);
    Value::local(ptr)
  }

  pub fn deref<'t>(
    inner: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    let ptr = function.flatten(inner, mir, block, fn_types);
    Value::lvalue(Lvalue::Deref(ptr))
  }

  // -- binops --
  pub fn add<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Add(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn sub<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Sub(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn mul<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Mul(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn div<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Div(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn rem<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Rem(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn and<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::And(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn xor<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Xor(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn or<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Or(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn shl<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Shl(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn shr<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Shr(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }

  // -- comparisons --
  pub fn eq<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Eq(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn neq<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block, fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Neq(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn lt<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Lt(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn lte<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Lte(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn gt<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Gt(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }
  pub fn gte<'t>(
    lhs: Self,
    rhs: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    Value(ValueKind::Gte(
      function.flatten(lhs, mir, block, fn_types),
      function.flatten(rhs, mir, block, fn_types),
    ))
  }

  // -- misc --
  pub fn call<'t>(
    callee: String,
    args: Vec<Self>,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    let args = args
      .into_iter()
      .map(|v| function.flatten(v, mir, block, fn_types))
      .collect();
    Value(ValueKind::Call {
      callee: callee,
      args: args,
    })
  }
}

impl Value {
  fn ty<'t>(
    &self,
    mir: &Mir<'t>,
    function: &Function<'t>,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Type<'t> {
    match self.0 {
      ValueKind::Literal(ref lit) => lit.ty(mir, function),
      ValueKind::Parameter(par) => function.get_param_ty(par),
      ValueKind::Lvalue(ref lv) => lv.ty(function),

      ValueKind::Pos(inner) | ValueKind::Neg(inner) | ValueKind::Not(inner)
      => function.get_local_ty(inner),

      ValueKind::Ref(inner)
      => Type::ref_(function.get_local_ty(inner), mir.ctxt),

      ValueKind::Add(lhs, rhs)
      | ValueKind::Sub(lhs, rhs)
      | ValueKind::Mul(lhs, rhs)
      | ValueKind::Div(lhs, rhs)
      | ValueKind::Rem(lhs, rhs)
      | ValueKind::And(lhs, rhs)
      | ValueKind::Xor(lhs, rhs)
      | ValueKind::Or(lhs, rhs)
      => {
        let lhs_ty = function.get_local_ty(lhs);
        assert_eq!(lhs_ty, function.get_local_ty(rhs));
        lhs_ty
      },

      ValueKind::Shl(lhs, _) | ValueKind::Shr(lhs, _)
      => function.get_local_ty(lhs),

      ValueKind::Eq(_, _)
      | ValueKind::Neq(_, _)
      | ValueKind::Lt(_, _)
      | ValueKind::Lte(_, _)
      | ValueKind::Gt(_, _)
      | ValueKind::Gte(_, _)
      => Type::bool(mir.ctxt),

      ValueKind::Call {
        ref callee,
        ..
      } =>  {
        fn_types.get(callee).expect("ICE: no function prototype")
          .output()
      },
    }
  }

  fn llvm_store<'t>(
    self,
    dst: llvm::Value,
    mir: &Mir<'t>,
    function: &mut LlFunction<'t>,
    funcs: &HashMap<String, (llvm::Value, Type<'t>)>,
  ) {
    let val = match self.0 {
      ValueKind::Literal(lit) => {
        lit.llvm_store(dst, function);
        return;
      }
      ValueKind::Parameter(par) => llvm::Value::get_param(function.raw, par.0),
      ValueKind::Lvalue(lv) => {
        let ptr = lv.to_llvm(function);
        function.builder.build_load(ptr)
      },
      ValueKind::Pos(inner) => {
        let ty = function.mir.get_local_ty(inner);
        let llinner = function.get_local_value(inner);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) => llinner,
          _ => panic!("ICE: {} can't be used in unary +", ty),
        }
      },
      ValueKind::Neg(inner) => {
        let ty = function.mir.get_local_ty(inner);
        let llinner = function.get_local_value(inner);
        match *ty.0 {
          TypeVariant::SInt(_) => function.builder.build_neg(llinner),
          _ => panic!("ICE: {} can't be used in unary -", ty),
        }
      },
      ValueKind::Not(inner) => {
        let ty = function.mir.get_local_ty(inner);
        let llinner = function.get_local_value(inner);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_not(llinner),
          _ => panic!("ICE: {} can't be used in unary !", ty),
        }
      }
      ValueKind::Ref(inner) => function.get_local_ptr(inner),
      ValueKind::Add(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_)
          => function.builder.build_add(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary +", ty),
        }
      }
      ValueKind::Sub(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_)
          => function.builder.build_sub(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary -", ty),
        }
      }
      ValueKind::Mul(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_)
          => function.builder.build_mul(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary *", ty),
        }
      }
      ValueKind::Div(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) => function.builder.build_sdiv(lhs, rhs),
          TypeVariant::UInt(_) => function.builder.build_udiv(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary /", ty),
        }
      }
      ValueKind::Rem(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) => function.builder.build_srem(lhs, rhs),
          TypeVariant::UInt(_) => function.builder.build_urem(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary %", ty),
        }
      }
      ValueKind::And(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_and(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary %", ty),
        }
      }
      ValueKind::Xor(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_xor(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary %", ty),
        }
      }
      ValueKind::Or(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_or(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary %", ty),
        }
      }
      ValueKind::Shl(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_)
          => function.builder.build_shl(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary %", ty),
        }
      }
      ValueKind::Shr(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) => function.builder.build_ashr(lhs, rhs),
          TypeVariant::UInt(_) => function.builder.build_lshr(lhs, rhs),
          _ => panic!("ICE: {} can't be used in binary %", ty),
        }
      }
      ValueKind::Eq(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_icmp(llvm::IntEQ, lhs, rhs),
          _ =>  panic!("ICE: {} can't be used in ==", ty),
        }
      }
      ValueKind::Neq(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_) | TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_icmp(llvm::IntNE, lhs, rhs),
          _ =>  panic!("ICE: {} can't be used in !=", ty),
        }
      }
      ValueKind::Lt(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_)
          => function.builder.build_icmp(llvm::IntSLT, lhs, rhs),
          TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_icmp(llvm::IntULT, lhs, rhs),
          _ =>  panic!("ICE: {} can't be used in <", ty),
        }
      }
      ValueKind::Lte(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_)
          => function.builder.build_icmp(llvm::IntSLE, lhs, rhs),
          TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_icmp(llvm::IntULE, lhs, rhs),
          _ =>  panic!("ICE: {} can't be used in <=", ty),
        }
      }
      ValueKind::Gt(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_)
          => function.builder.build_icmp(llvm::IntSGT, lhs, rhs),
          TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_icmp(llvm::IntUGT, lhs, rhs),
          _ =>  panic!("ICE: {} can't be used in >", ty),
        }
      }
      ValueKind::Gte(lhs, rhs) => {
        let ty = function.mir.get_local_ty(lhs);
        let lhs = function.get_local_value(lhs);
        let rhs = function.get_local_value(rhs);
        match *ty.0 {
          TypeVariant::SInt(_)
          => function.builder.build_icmp(llvm::IntSGE, lhs, rhs),
          TypeVariant::UInt(_) | TypeVariant::Bool
          => function.builder.build_icmp(llvm::IntUGE, lhs, rhs),
          _ =>  panic!("ICE: {} can't be used in >=", ty),
        }
      }
      ValueKind::Call {
        callee,
        args,
      } => {
        let args = args
          .into_iter()
          .map(|a| function.get_local_value(a))
          .collect::<Vec<_>>();
        let (callee, output) = *funcs.get(&callee).unwrap();
        let llret = function.builder.build_call(callee, &args);

        if llvm::size_of_type(&mir.target_data, output) == 0 {
          llvm::Value::const_nil()
        } else {
          llret
        }
      }
    };
    function.builder.build_store(dst, val);
  }
}

#[derive(Copy, Clone, Debug)]
enum Lvalue {
  Local(Local),
  Deref(Local),
  Return,
}

impl Lvalue {
  fn ty<'t>(&self, function: &Function<'t>) -> Type<'t> {
    match *self {
      Lvalue::Local(l) => function.get_local_ty(l),
      Lvalue::Deref(l) => {
        let outer_ty = function.get_local_ty(l);
        if let TypeVariant::Reference(inner) = *outer_ty.0 {
          inner
        } else {
          panic!("ICE: Attempt to take type of a deref of {:?}", outer_ty);
        }
      }
      Lvalue::Return => {
        function.ty.output()
      }
    }
  }

  fn to_llvm(self, function: &LlFunction) -> llvm::Value {
    match self {
      Lvalue::Local(loc) => {
        function.get_local_ptr(loc)
      }
      Lvalue::Deref(loc) => {
        function.get_local_value(loc)
      }
      Lvalue::Return => {
        function.ret_ptr
      }
    }
  }
}

#[derive(Debug)]
struct Statement(Lvalue, Value);

impl Statement {
  fn to_llvm<'t>(
    self,
    mir: &Mir<'t>,
    function: &mut LlFunction<'t>,
    funcs: &HashMap<String, (llvm::Value, Type<'t>)>,
  ) {
    let dst = (self.0).to_llvm(function);
    let src = (self.1).llvm_store(dst, mir, function, funcs);
  }
}

#[derive(Debug)]
enum Terminator {
  Goto(Block),
  If {
    cond: Local,
    then_blk: Block,
    else_blk: Block,
  },
  // Normal return; should only happen in the end block
  Return,
}

impl Terminator {
  fn to_llvm<'t>(self, mir: &Mir<'t>, function: &LlFunction<'t>) {
    match self {
      Terminator::Goto(mut b) => {
        function.builder.build_br(function.get_block(&mut b));
      },
      Terminator::If {
        cond,
        mut then_blk,
        mut else_blk,
      } => {
        let cond = function.get_local_value(cond);
        function.builder.build_cond_br(
          cond,
          function.get_block(&mut then_blk),
          function.get_block(&mut else_blk),
        );
      }
      Terminator::Return => {
        if llvm::size_of_type(&mir.target_data, function.mir.ty.output()) == 0 {
          function.builder.build_void_ret();
        } else {
          let value = function.builder.build_load(function.ret_ptr);
          function.builder.build_ret(value);
        }
      }
    }
  }
}

#[derive(Debug, PartialEq)]
pub struct Block(usize);

impl Block {
  pub fn set(&mut self, loc: Local, val: Value, function: &mut Function) {
    self.add_stmt(Lvalue::Local(loc), val, function)
  }

  pub fn store<'t>(
    &mut self,
    ptr: Value,
    val: Value,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) {
    let local = function.flatten(ptr, mir, self, fn_types);
    self.add_stmt(Lvalue::Deref(local), val, function)
  }

  pub fn set_tmp<'t>(
    &mut self,
    val: Value,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Value {
    let ty = val.ty(mir, function, fn_types);
    let tmp = function.new_local(ty);
    self.add_stmt(Lvalue::Local(tmp), val, function);
    Value::local(tmp)
  }

  fn add_stmt(
    &mut self,
    lvalue: Lvalue,
    value: Value,
    function: &mut Function,
  ) {
    let blk = function.get_block(self);
    blk.statements.push(Statement(lvalue, value))
  }
}
// terminators
impl Block {
  pub fn if_else<'t>(
    mut self,
    ty: Type<'t>,
    cond: Value,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> (Block, Block, Block, Value) {
    let cond = function.flatten(cond, mir, &mut self, fn_types);
    let tmp = function.new_local(ty);

    let mut then = function.new_block(Lvalue::Local(tmp),
      Terminator::Return);
    let mut else_ = function.new_block(Lvalue::Local(tmp),
      Terminator::Return);
    // terminator is not permanent

    let (expr, term) = {
      let blk = function.get_block(&mut self);
      let term = std::mem::replace(&mut blk.terminator,
        Terminator::If {
          cond: cond,
          then_blk: Block(then.0),
          else_blk: Block(else_.0)
        });
      (blk.expr, term)
    };
    let join = function.new_block(expr, term);

    {
      let then_blk = function.get_block(&mut then);
      then_blk.terminator = Terminator::Goto(Block(join.0));
    }
    {
      let else_blk = function.get_block(&mut else_);
      else_blk.terminator = Terminator::Goto(Block(join.0));
    }

    (then, else_, join, Value::local(tmp))
  }

  pub fn early_ret(mut self, function: &mut Function, value: Value) {
    let blk = function.get_block(&mut self);
    blk.statements.push(Statement(Lvalue::Return, value));
    blk.terminator = Terminator::Goto(END_BLOCK);
  }

  pub fn finish(mut self, function: &mut Function, value: Value) {
    let blk = function.get_block(&mut self);
    blk.statements.push(Statement(blk.expr, value));
  }

  fn terminate(&mut self, function: &mut Function, terminator: Terminator) {
    let blk = function.get_block(self);
    blk.terminator = terminator;
  }
}

#[derive(Debug)]
struct BlockData {
  expr: Lvalue,
  statements: Vec<Statement>,
  terminator: Terminator,
}

impl BlockData {
  fn new(expr: Lvalue, term: Terminator) -> BlockData {
    BlockData {
      expr: expr,
      statements: Vec::new(),
      terminator: term,
    }
  }
}

pub struct Mir<'t> {
  functions: HashMap<String, Function<'t>>,
  ctxt: &'t TypeContext<'t>,

  optimize: bool,

  target_machine: llvm::TargetMachine,
  target_data: llvm::TargetData,
}

impl<'t> Mir<'t> {
  pub fn new(ctxt: &'t TypeContext<'t>, opt: bool) -> Mir<'t> {
    let opt_level = if opt {
      llvm::NoOptimization
    } else {
      llvm::DefaultOptimization
    };
    let target_machine = llvm::TargetMachine::new(opt_level).unwrap();
    let target_data =
      llvm::TargetData::from_target_machine(&target_machine);

    Mir {
      functions: HashMap::new(),
      ctxt: ctxt,
      optimize: opt,
      target_machine: target_machine,
      target_data: target_data,
    }
  }

  pub fn add_function(&mut self, name: String, func: Function<'t>) {
    self.functions.insert(name, func);
  }

  pub fn build_and_write(mut self, output: &str, print_llir: ::DebugPrint) {
    let mut llvm_functions = HashMap::new();
    let module = llvm::Module::new();

    let optimizer = llvm::FnOptimizer::for_module(&module);

    for (name, function) in &self.functions {
      let llfunc = module.add_function(
        &name,
        llvm::get_function_type(&self.target_data, &function.ty),
      );
      llvm_functions.insert(
        name.clone(),
        (llfunc, function.ty.output()),
      );
    }

    let functions = std::mem::replace(&mut self.functions, HashMap::new());
    for (name, function) in functions {
      let llfunc = llvm_functions.get(&name).unwrap().0;
      function.build(&self, llfunc, &llvm_functions);
      if self.optimize {
        optimizer.optimize(llfunc);
      }
    }

    if let ::DebugPrint::Print = print_llir {
      module.dump();
    }

    module.verify();

    match self.target_machine.emit_to_file(&module, output) {
      Ok(()) => {},
      Err(e) => panic!("Failed to write to output file: {:?}", e),
    }
  }

  #[inline(always)]
  pub fn ty_ctxt(&self) -> &'t TypeContext<'t> {
    self.ctxt
  }
}
