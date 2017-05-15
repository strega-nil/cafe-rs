use std;
use std::collections::HashMap;
use ty::{self, Type, TypeContext};

mod fmt;
mod interpret;

const START_BLOCK: Block = Block(0);
const END_BLOCK: Block = Block(1);

#[derive(Debug)]
pub struct Function<'t> {
  ty: ty::Function<'t>,
  stack_frame: Vec<Type<'t>>,
  blocks: Vec<BlockData>,
  //param_names: Vec<String>,
  bindings: Vec<(Type<'t>, String)>,
}

#[derive(Copy, Clone, Debug)]
pub struct Binding(u32);

#[derive(Copy, Clone, Debug)]
struct Local(u32);
#[derive(Copy, Clone, Debug)]
struct Parameter(u32);

impl<'t> Function<'t> {
  pub fn new(ty: ty::Function<'t>, param_names: Vec<String>) -> Self {
    let mut ret = Function {
      ty: ty,
      stack_frame: vec![],
      blocks: vec![],
      bindings: vec![],
    };
    assert_eq!(
      START_BLOCK,
      ret.new_block(Binding(0), Terminator::Goto(END_BLOCK))
    );
    assert_eq!(
      END_BLOCK,
      ret.new_block(Binding(0), Terminator::Return)
    );
    let typ = ret.ty.output();
    ret.new_local(typ, None);
    let input_types = ret.ty.input().to_owned();
    {
      assert_eq!(input_types.len(), param_names.len());
      for (ty, name) in input_types.iter().zip(param_names) {
        ret.new_local(*ty, Some(name));
      }
      let blk = ret.get_block(&mut START_BLOCK);
      for i in 0..input_types.len() as u32 {
        blk.statements.push(Statement::Assign(
          Binding(i + 1),
          Value(ValueKind::Parameter(Parameter(i)))
        ))
      }
    }
    END_BLOCK.terminate(&mut ret, Terminator::Return);
    ret
  }

  pub fn start_block(&self) -> Block {
    START_BLOCK
  }

  fn new_block(&mut self, expr: Binding, term: Terminator) -> Block {
    self.blocks.push(BlockData::new(expr, term));
    Block(self.blocks.len() - 1)
  }
  pub fn new_local(&mut self, ty: Type<'t>, name: Option<String>) -> Binding {
    assert!(self.stack_frame.len() < u32::max_value() as usize);
    self.stack_frame.push(ty);
    self.bindings.push((ty, name.unwrap_or("".to_owned())));
    Binding(self.bindings.len() as u32 - 1)
  }
  pub fn get_param_local(&mut self, n: u32) -> Binding {
    assert!(n < self.ty.input().len() as u32);
    Binding(n + 1) // TODO(ubsan): stack binding
  }

  fn get_block(&mut self, blk: &mut Block) -> &mut BlockData {
    &mut self.blocks[blk.0 as usize]
  }
  fn get_param_ty(&self, par: Parameter) -> Type<'t> {
    self.ty.input()[par.0 as usize]
  }
  fn get_local_ty(&self, var: Local) -> Type<'t> {
    self.stack_frame[var.0 as usize]
  }
  fn get_binding_ty(&self, var: Binding) -> Type<'t> {
    self.bindings[var.0 as usize].0
  }

  fn flatten(
    &mut self,
    value: Value,
    mir: &Mir<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Binding {
    if let ValueKind::Binding(bind) = value.0 {
      bind
    } else {
      let ty = value.ty(mir, self, fn_types);
      let tmp = self.new_local(ty, None);
      block.add_assign(tmp, value, self);
      tmp
    }
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
  Unit,
}

impl Literal {
  fn ty<'t>(&self, mir: &Mir<'t>) -> Type<'t> {
    match *self {
      Literal::Int {
        ty,
        signed,
        value: _,
      } => if signed {
        Type::sint(ty, mir.ctxt)
      } else {
        Type::uint(ty, mir.ctxt)
      },
      Literal::Bool(_) => Type::bool(mir.ctxt),
      Literal::Unit => {
        Type::unit(mir.ctxt)
      }
    }
  }
}

#[derive(Clone, Debug)]
enum ValueKind {
  Literal(Literal),
  Parameter(Parameter),

  Binding(Binding),

  // -- unops --
  Pos(Binding),
  Neg(Binding),
  Not(Binding),

  // -- binops --
  Add(Binding, Binding),
  Sub(Binding, Binding),
  Mul(Binding, Binding),
  Div(Binding, Binding),
  Rem(Binding, Binding),
  And(Binding, Binding),
  Xor(Binding, Binding),
  Or(Binding, Binding),
  Shl(Binding, Binding),
  Shr(Binding, Binding),

  // -- comparison --
  Eq(Binding, Binding),
  Neq(Binding, Binding),
  Lt(Binding, Binding),
  Lte(Binding, Binding),
  Gt(Binding, Binding),
  Gte(Binding, Binding),

  // -- other --
  Log(Binding),
  Call {
    callee: String,
    args: Vec<Binding>,
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
  #[inline(always)]
  pub fn unit_literal() -> Value {
    Value(ValueKind::Literal(Literal::Unit))
  }

  #[inline(always)]
  pub fn param(arg_num: u32, function: &mut Function) -> Self {
    assert!(arg_num < function.ty.input().len() as u32);
    Value::binding(function.get_param_local(arg_num))
  }
  #[inline(always)]
  pub fn binding(bind: Binding) -> Self {
    Value(ValueKind::Binding(bind))
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

  pub fn log<'t>(
    arg: Self,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    block: &mut Block,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Self {
    let value = function.flatten(arg, mir, block, fn_types);
    Value(ValueKind::Log(value))
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
      ValueKind::Literal(ref lit) => lit.ty(mir),
      ValueKind::Parameter(par) => function.get_param_ty(par),
      ValueKind::Binding(bind) => function.get_binding_ty(bind),

      ValueKind::Pos(inner) | ValueKind::Neg(inner) | ValueKind::Not(inner)
      => function.get_binding_ty(inner),

      ValueKind::Add(lhs, rhs)
      | ValueKind::Sub(lhs, rhs)
      | ValueKind::Mul(lhs, rhs)
      | ValueKind::Div(lhs, rhs)
      | ValueKind::Rem(lhs, rhs)
      | ValueKind::And(lhs, rhs)
      | ValueKind::Xor(lhs, rhs)
      | ValueKind::Or(lhs, rhs)
      => {
        let lhs_ty = function.get_binding_ty(lhs);
        assert_eq!(lhs_ty, function.get_binding_ty(rhs));
        lhs_ty
      },

      ValueKind::Shl(lhs, _) | ValueKind::Shr(lhs, _)
      => function.get_binding_ty(lhs),

      ValueKind::Eq(_, _)
      | ValueKind::Neq(_, _)
      | ValueKind::Lt(_, _)
      | ValueKind::Lte(_, _)
      | ValueKind::Gt(_, _)
      | ValueKind::Gte(_, _)
      => Type::bool(mir.ctxt),

      ValueKind::Log(_) => Type::unit(mir.ctxt),
      ValueKind::Call {
        ref callee,
        ..
      } => {
        fn_types.get(callee).expect("ICE: no function prototype")
          .output()
      },
    }
  }
}

#[derive(Copy, Clone, Debug)]
enum Lvalue {
  Local(Local),
}

#[allow(dead_code)]
impl Lvalue {
  fn ty<'t>(&self, function: &Function<'t>) -> Type<'t> {
    match *self {
      Lvalue::Local(l) => function.get_local_ty(l),
    }
  }
}

#[derive(Debug)]
enum Statement {
  Assign(Binding, Value),
  Bind(Binding, Lvalue),
}

#[derive(Debug)]
enum Terminator {
  Goto(Block),
  If {
    cond: Binding,
    then_blk: Block,
    else_blk: Block,
  },
  // Normal return; should only happen in the end block
  Return,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Block(usize);

impl Block {
  pub fn set(&mut self, bind: Binding, val: Value, function: &mut Function) {
    self.add_assign(bind, val, function)
  }

  pub fn set_tmp<'t>(
    &mut self,
    val: Value,
    mir: &Mir<'t>,
    function: &mut Function<'t>,
    fn_types: &HashMap<String, ty::Function<'t>>,
  ) -> Value {
    let ty = val.ty(mir, function, fn_types);
    let tmp = function.new_local(ty, None);
    self.add_assign(tmp, val, function);
    Value::binding(tmp)
  }

  fn add_assign(
    &mut self,
    binding: Binding,
    value: Value,
    function: &mut Function,
  ) {
    let blk = function.get_block(self);
    blk.statements.push(Statement::Assign(binding, value))
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
    let tmp = function.new_local(ty, None);

    let mut then = function.new_block(tmp, Terminator::Return);
    let mut else_ = function.new_block(tmp, Terminator::Return);
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

    (then, else_, join, Value::binding(tmp))
  }

  pub fn early_ret(mut self, function: &mut Function, value: Value) {
    let blk = function.get_block(&mut self);
    blk.statements.push(Statement::Assign(Binding(0), value));
    blk.terminator = Terminator::Goto(END_BLOCK);
  }

  pub fn finish(mut self, function: &mut Function, value: Value) {
    let blk = function.get_block(&mut self);
    blk.statements.push(Statement::Assign(blk.expr, value));
  }

  fn terminate(&mut self, function: &mut Function, terminator: Terminator) {
    let blk = function.get_block(self);
    blk.terminator = terminator;
  }
}

#[derive(Debug)]
struct BlockData {
  // TODO(ubsan): remove this
  expr: Binding,
  statements: Vec<Statement>,
  terminator: Terminator,
}

impl BlockData {
  fn new(expr: Binding, terminator: Terminator) -> BlockData {
    BlockData {
      expr,
      statements: Vec::new(),
      terminator,
    }
  }
}

pub struct Mir<'t> {
  functions: HashMap<String, Function<'t>>,
  ctxt: &'t TypeContext<'t>,
}

impl<'t> Mir<'t> {
  pub fn new(ctxt: &'t TypeContext<'t>) -> Mir<'t> {
    Mir {
      functions: HashMap::new(),
      ctxt: ctxt,
    }
  }

  pub fn add_function(&mut self, name: String, func: Function<'t>) {
    self.functions.insert(name, func);
  }

  #[inline(always)]
  pub fn ty_ctxt(&self) -> &'t TypeContext<'t> {
    self.ctxt
  }
}
