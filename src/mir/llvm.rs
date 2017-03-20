use std;
use std::ffi::{CStr, CString};
use ty;

extern crate llvm_sys;
extern crate libc;
use self::libc::c_char;
use self::llvm_sys::*;
use self::llvm_sys::prelude::*;
use self::llvm_sys::core::*;
use self::llvm_sys::target::*;
use self::llvm_sys::target_machine::*;
use self::llvm_sys::transforms::scalar::*;
use self::llvm_sys::analysis::*;

// TODO(ubsan): ZSTs should not be passed into functions


#[allow(non_upper_case_globals)]
const LLFalse: LLVMBool = false as LLVMBool;
#[allow(unused, non_upper_case_globals)]
const LLTrue: LLVMBool = true as LLVMBool;

macro_rules! cstr {
  ($s:expr) => (
    concat!($s, "\0").as_ptr() as *const self::libc::c_char
  )
}

pub use self::llvm_sys::LLVMIntPredicate::{
  LLVMIntEQ as IntEQ,
  LLVMIntNE as IntNE,
  LLVMIntUGT as IntUGT,
  LLVMIntUGE as IntUGE,
  LLVMIntULT as IntULT,
  LLVMIntULE as IntULE,
  LLVMIntSGT as IntSGT,
  LLVMIntSGE as IntSGE,
  LLVMIntSLT as IntSLT,
  LLVMIntSLE as IntSLE,
};

pub use self::llvm_sys::target_machine::LLVMCodeGenOptLevel::{
  LLVMCodeGenLevelNone as NoOptimization,
  LLVMCodeGenLevelLess as LessOptimization,
  LLVMCodeGenLevelDefault as DefaultOptimization,
  LLVMCodeGenLevelAggressive as AggressiveOptimization,
};


#[derive(Copy, Clone, Debug)]
pub struct Value(LLVMValueRef);
impl Value {
  pub fn const_int(ty: Type, value: u64) -> Value {
    unsafe {
      Value(LLVMConstInt(ty.0, value, LLFalse))
    }
  }

  pub fn const_bool(value: bool) -> Value {
    unsafe {
      Value(LLVMConstInt(LLVMInt1Type(), value as u64, LLFalse))
    }
  }

  pub fn const_nil() -> Value {
    println!("const struct");
    let ret = unsafe {
      Value(LLVMConstStruct(std::ptr::null_mut(), 0, LLFalse))
    };
    println!("end const struct");
    ret
  }

  pub fn make_struct(
    dst: Value,
    builder: &Builder,
    values: &[Value],
  ) {
    unsafe {
      let mut llvm_types = vec![];
      for val in values {
        llvm_types.push(val.get_llvm_type());
      }
      builder.build_store(
        dst,
        Value(LLVMGetUndef(LLVMStructType(
          llvm_types.as_mut_ptr(),
          llvm_types.len() as std::os::raw::c_uint,
          LLFalse,
        ))),
      );
      for (i, val) in values.iter().enumerate() {
        builder.build_store(
          Value(LLVMBuildStructGEP(
            builder.0,
            dst.0,
            i as std::os::raw::c_uint,
            cstr!(""),
          )),
          *val,
        );
      }
    }
  }

  fn get_llvm_type(&self) -> LLVMTypeRef {
    unsafe {
      LLVMTypeOf(self.0)
    }
  }

  pub fn get_param(func: Value, number: u32) -> Value {
    unsafe {
      Value(LLVMGetParam(func.0, number))
    }
  }

  fn llvm_slice(value_slice: &[Value]) -> &[LLVMValueRef] {
    #[allow(dead_code)]
    unsafe fn size_of_value_is_size_of_value_ref() {
      std::mem::transmute::<LLVMValueRef, Value>(std::ptr::null_mut());
    }
    unsafe {
      std::slice::from_raw_parts(
        value_slice.as_ptr() as *const LLVMValueRef,
        value_slice.len(),
      )
    }
  }

  #[allow(dead_code)]
  pub fn dump(self) {
    unsafe {
      LLVMDumpValue(self.0)
    }
  }
}

#[derive(Debug)]
pub struct Builder(LLVMBuilderRef);
impl Builder {
  pub fn new() -> Self {
    unsafe {
      Builder(LLVMCreateBuilder())
    }
  }

  pub fn position_at_end(&self, blk: BasicBlock) {
    unsafe {
      LLVMPositionBuilderAtEnd(self.0, blk.0);
    }
  }

  pub fn build_call(&self, callee: Value, args: &[Value]) -> Value {
    unsafe {
      let args = Value::llvm_slice(args);
      let len = args.len() as u32;
      Value(LLVMBuildCall(self.0, callee.0,
        args.as_ptr() as *mut _, len, cstr!("")))
    }
  }

  pub fn build_br(&self, block: BasicBlock) {
    unsafe {
      LLVMBuildBr(self.0, block.0);
    }
  }

  pub fn build_cond_br(&self, cond: Value,
      then: BasicBlock, else_: BasicBlock) {
    unsafe {
      LLVMBuildCondBr(self.0, cond.0, then.0, else_.0);
    }
  }

  pub fn build_ret(&self, ret: Value) {
    unsafe {
      LLVMBuildRet(self.0, ret.0);
    }
  }

  pub fn build_void_ret(&self) {
    unsafe {
      LLVMBuildRetVoid(self.0);
    }
  }

  pub fn build_alloca(&self, ty: Type, name: &str) -> Value {
    unsafe {
      Value(LLVMBuildAlloca(self.0, ty.0,
        CString::new(name.to_owned()).unwrap().as_ptr()))
    }
  }

  pub fn build_load(&self, ptr: Value) -> Value {
    unsafe {
      Value(LLVMBuildLoad(self.0, ptr.0, cstr!("")))
    }
  }

  pub fn build_store(&self, dst: Value, src: Value) {
    unsafe {
      LLVMBuildStore(self.0, src.0, dst.0);
    }
  }

  pub fn build_neg(&self, inner: Value) -> Value {
    unsafe {
      Value(LLVMBuildNeg(self.0, inner.0, cstr!("")))
    }
  }

  pub fn build_not(&self, inner: Value) -> Value {
    unsafe {
      Value(LLVMBuildNot(self.0, inner.0, cstr!("")))
    }
  }

  pub fn build_add(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildAdd(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_sub(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildSub(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_mul(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildMul(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_udiv(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildUDiv(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_sdiv(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildSDiv(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_urem(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildURem(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_srem(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildSRem(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }

  pub fn build_and(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildAnd(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_xor(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildXor(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_or(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildOr(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }

  pub fn build_shl(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildShl(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_ashr(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildAShr(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }
  pub fn build_lshr(&self, lhs: Value, rhs: Value) -> Value {
    unsafe {
      Value(LLVMBuildLShr(self.0, lhs.0, rhs.0, cstr!("")))
    }
  }

  pub fn build_icmp(&self, pred: LLVMIntPredicate, lhs: Value, rhs: Value)
      -> Value {
    unsafe {
      Value(LLVMBuildICmp(self.0, pred, lhs.0, rhs.0, cstr!("")))
    }
  }
}

impl std::ops::Drop for Builder {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeBuilder(self.0)
    }
  }
}

#[derive(Copy, Clone, Debug)]
pub struct BasicBlock(LLVMBasicBlockRef);
impl BasicBlock {
  pub fn append(func: Value, num: u32) -> Self {
    unsafe {
      BasicBlock(LLVMAppendBasicBlock(func.0,
        CString::new(format!("bb{}", num)).unwrap().as_ptr()))
    }
  }
}

pub struct Type(LLVMTypeRef);

#[derive(Copy, Clone, Debug)]
pub enum TargetMachineError {
  CouldntInitNativeTarget,
  CouldntInitNativeAsmPrinter,
  CouldntGetTargetFromTriple,
}

#[derive(Debug)]
pub struct TargetMachine(LLVMTargetMachineRef);
impl TargetMachine {
  pub fn new(opt_level: LLVMCodeGenOptLevel)
      -> Result<Self, TargetMachineError> {
    unsafe {
      if LLVM_InitializeNativeTarget() != 0 {
        return Err(TargetMachineError::CouldntInitNativeTarget);
      }
      if LLVM_InitializeNativeAsmPrinter() != 0 {
        return Err(TargetMachineError::CouldntInitNativeAsmPrinter);
      }
      let triple = LLVMGetDefaultTargetTriple();
      let mut target = std::mem::uninitialized();
      if LLVMGetTargetFromTriple(triple, &mut target,
          std::ptr::null_mut()) != 0 {
        return Err(TargetMachineError::CouldntGetTargetFromTriple);
      }


      Ok(TargetMachine(LLVMCreateTargetMachine(target, triple, cstr!(""),
        cstr!(""), opt_level, LLVMRelocMode::LLVMRelocDefault,
        LLVMCodeModel::LLVMCodeModelDefault)))
    }
  }

  pub fn emit_to_file(&self, module: &Module, output: &str)
      -> Result<(), String> {
    let output = CString::new(output.to_owned()).unwrap();
    unsafe {
      let mut error = std::mem::uninitialized();
      if LLVMTargetMachineEmitToFile(self.0, module.0,
          output.as_ptr() as *mut c_char,
          LLVMCodeGenFileType::LLVMObjectFile, &mut error) != 0 {
        Err(CStr::from_ptr(error).to_string_lossy().into_owned())
      } else {
        Ok(())
      }
    }
  }
}

impl std::ops::Drop for TargetMachine {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeTargetMachine(self.0);
    }
  }
}

#[derive(Debug)]
pub struct TargetData(LLVMTargetDataRef);
impl TargetData {
  pub fn from_target_machine(machine: &TargetMachine) -> Self {
    unsafe {
      TargetData(LLVMGetTargetMachineData(machine.0))
    }
  }
}

pub struct Module(LLVMModuleRef);
impl Module {
  pub fn new() -> Self {
    unsafe {
      Module(LLVMModuleCreateWithName(cstr!("")))
    }
  }

  pub fn add_function(&self, name: &str, ty: Type) -> Value {
    unsafe {
      Value(LLVMAddFunction(self.0,
        CString::new(name.to_owned()).unwrap().as_ptr(), ty.0))
    }
  }

  pub fn dump(&self) {
    unsafe {
      LLVMDumpModule(self.0)
    }
  }

  pub fn verify(&self) {
    unsafe {
      let mut error: *mut c_char = std::mem::uninitialized();
      LLVMVerifyModule(self.0,
        LLVMVerifierFailureAction::LLVMAbortProcessAction, &mut error);
      LLVMDisposeMessage(error);
    }
  }
}

impl std::ops::Drop for Module {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposeModule(self.0);
    }
  }
}

pub struct FnOptimizer(LLVMPassManagerRef);
impl FnOptimizer {
  pub fn for_module(module: &Module) -> Self {
    unsafe {
      let pm = LLVMCreateFunctionPassManagerForModule(module.0);

      // NOTE(ubsan): add optimizations here
      LLVMAddBasicAliasAnalysisPass(pm);
      LLVMAddInstructionCombiningPass(pm);
      LLVMAddReassociatePass(pm);
      LLVMAddGVNPass(pm);
      LLVMAddCFGSimplificationPass(pm);
      LLVMAddDeadStoreEliminationPass(pm);
      LLVMInitializeFunctionPassManager(pm);
      FnOptimizer(pm)
    }
  }

  pub fn optimize(&self, func: Value) {
    unsafe {
      LLVMVerifyFunction(func.0,
        LLVMVerifierFailureAction::LLVMAbortProcessAction);
      LLVMRunFunctionPassManager(self.0, func.0);
    }
  }
}

impl std::ops::Drop for FnOptimizer {
  fn drop(&mut self) {
    unsafe {
      LLVMDisposePassManager(self.0)
    }
  }
}


pub fn size_of_type(target_data: &TargetData, ty: ty::Type) -> u64 {
  unsafe {
    if let ty::TypeVariant::Diverging = *ty.0 {
      0
    } else {
      LLVMSizeOfTypeInBits(target_data.0, get_type(target_data, ty).0)
    }
  }
}

pub fn get_int_type(ty: ty::Int) -> Type {
  unsafe {
    Type(LLVMIntType(ty.size()))
  }
}

pub fn get_type(target_data: &TargetData, ty: ty::Type) -> Type {
  use ty::TypeVariant;
  unsafe {
    Type(match *ty.0 {
      TypeVariant::SInt(ref size) | TypeVariant::UInt(ref size)
        => LLVMIntType(size.size()),
      TypeVariant::Bool => LLVMInt1Type(),
      TypeVariant::Reference(inner) =>
        LLVMPointerType(get_type(target_data, inner).0, 0),
      TypeVariant::Tuple(ref v) => {
        let mut llvm =
          v.iter().map(|el| get_type(target_data, *el).0)
            .collect::<Vec<_>>();
        LLVMStructType(llvm.as_mut_ptr(), llvm.len() as u32, LLFalse)
      }
      TypeVariant::Diverging
        => panic!("ICE: Attempted to get the LLVM type of \
          Diverging"),
      TypeVariant::Infer(_) | TypeVariant::InferInt(_) =>
        panic!("ICE: Attempted to get the LLVM type of an \
          inference variable: {:?}", ty),
    })
  }
}

pub fn get_return_type(target_data: &TargetData, ty: ty::Type) -> Type {
  unsafe {
    if size_of_type(target_data, ty) == 0 {
      Type(LLVMVoidType())
    } else {
      get_type(target_data, ty)
    }
  }
}

pub fn get_function_type(target_data: &TargetData, ty: &ty::Function)
    -> Type {
  unsafe {
    let mut args = ty.input().iter().map(|a| get_type(target_data, *a).0)
      .collect::<Vec<_>>();
    Type(LLVMFunctionType(
      get_return_type(target_data, ty.output()).0,
      args.as_mut_ptr(),
      args.len() as u32,
      LLFalse,
    ))
  }
}
