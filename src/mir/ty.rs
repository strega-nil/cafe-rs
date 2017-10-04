use parse::{Location, Spanned};
use super::align;

use std::{iter, slice};
use std::fmt::{self, Display};
use std::ops::{Deref, Index};

#[derive(Debug)]
pub enum TypeErrorVariant<'ctx> {
    TypeNotFound(String),
    BindingNotFound(String),
    Mismatched { lhs: Type<'ctx>, rhs: Type<'ctx> },
    NumberOfArgs {
        name: String,
        args_expected: u32,
        args_found: u32,
    },
}

impl<'ctx> Display for TypeErrorVariant<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeErrorVariant::*;
        match *self {
            TypeNotFound(ref s) => write!(f, "could not find type '{}'", s),
            BindingNotFound(ref s) => write!(f, "could not find name '{}'", s),
            Mismatched { lhs, rhs } => write!(f, "lhs ({}) != rhs ({})", lhs.name(), rhs.name()),
            NumberOfArgs {
                ref name,
                ref args_expected,
                ref args_found,
            } => write!(
                f,
                "function '{}' takes {} arguments, but {} arguments were passed",
                name,
                args_expected,
                args_found
            ),
        }
    }
}
pub type TypeError<'ctx> = Spanned<TypeErrorVariant<'ctx>>;

impl<'ctx> TypeError<'ctx> {
    pub fn type_not_found(name: String, start: Location, end: Option<Location>) -> Self {
        Spanned {
            thing: TypeErrorVariant::TypeNotFound(name),
            start,
            end,
        }
    }

    pub fn binding_not_found(name: String, start: Location, end: Option<Location>) -> Self {
        Spanned {
            thing: TypeErrorVariant::BindingNotFound(name),
            start,
            end,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum IntSize {
    //I8,
    //I16,
    I32,
    //I64,
    // ISize,
    // I128,
}
impl IntSize {
    fn size(self) -> u32 {
        match self {
            IntSize::I32 => 4,
        }
    }
}
#[derive(Debug)]
pub enum BuiltinType {
    SInt(IntSize),
    //UInt(IntSize),
    Bool,
    Unit,
}

impl BuiltinType {
    fn size(&self) -> u32 {
        match *self {
            BuiltinType::SInt(sz) => sz.size(),
            BuiltinType::Bool => 1,
            BuiltinType::Unit => 0,
        }
    }

    fn align(&self) -> u32 {
        match *self {
            BuiltinType::SInt(sz) => sz.size(),
            BuiltinType::Bool => 1,
            BuiltinType::Unit => 1,
        }
    }
}

#[derive(Debug)]
pub enum TypeVariant<'ctx> {
    Builtin(BuiltinType),
    __LifetimeHolder(::std::marker::PhantomData<&'ctx ()>),
}

impl<'ctx> TypeVariant<'ctx> {
    fn size(&self) -> u32 {
        match *self {
            TypeVariant::Builtin(ref builtin) => builtin.size(),
            TypeVariant::__LifetimeHolder(_) => unreachable!(),
        }
    }
    fn align(&self) -> u32 {
        match *self {
            TypeVariant::Builtin(ref builtin) => builtin.align(),
            TypeVariant::__LifetimeHolder(_) => unreachable!(),
        }
    }
}

#[derive(Debug)]
pub struct NamedType<'ctx> {
    ty: TypeVariant<'ctx>,
    name: String,
}

impl<'ctx> NamedType<'ctx> {
    pub fn s32() -> Self {
        Self {
            ty: TypeVariant::Builtin(BuiltinType::SInt(IntSize::I32)),
            name: "s32".to_owned(),
        }
    }

    pub fn bool() -> Self {
        Self {
            ty: TypeVariant::Builtin(BuiltinType::Bool),
            name: "bool".to_owned(),
        }
    }
    pub fn unit() -> Self {
        Self {
            ty: TypeVariant::Builtin(BuiltinType::Unit),
            name: "unit".to_owned(),
        }
    }

    pub fn size(&self) -> u32 {
        self.ty.size()
    }
    pub fn align(&self) -> u32 {
        self.ty.align()
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn variant(&self) -> &TypeVariant<'ctx> {
        &self.ty
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Type<'ctx>(&'ctx NamedType<'ctx>);
impl<'ctx> Type<'ctx> {
    pub fn new(inner: &'ctx NamedType<'ctx>) -> Self {
        Type(inner)
    }
}
impl<'ctx> PartialEq for Type<'ctx> {
    fn eq(&self, other: &Self) -> bool {
        self.0 as *const _ == other.0 as *const _
    }
}
impl<'ctx> Eq for Type<'ctx> {}
impl<'ctx> Deref for Type<'ctx> {
    type Target = NamedType<'ctx>;
    fn deref(&self) -> &NamedType<'ctx> {
        self.0
    }
}

pub struct BuiltinTypes<'ctx> {
    pub unit_ty: Type<'ctx>,
    pub bool_ty: Type<'ctx>,
    pub s32_ty: Type<'ctx>,
}

#[derive(Debug)]
pub struct TypeList<'ctx> {
    tys: Vec<Type<'ctx>>,
}

impl<'ctx> TypeList<'ctx> {
    pub fn new() -> Self {
        TypeList { tys: vec![] }
    }

    pub fn push(&mut self, ty: Type<'ctx>) {
        self.tys.push(ty);
    }

    pub fn from_existing(tys: Vec<Type<'ctx>>) -> Self {
        TypeList { tys }
    }

    pub fn number_of_types(&self) -> u32 {
        self.tys.len() as u32
    }

    pub fn is_empty(&self) -> bool {
        self.tys.is_empty()
    }

    // should really be cached
    // aligned to 16 bytes
    pub fn size(&self) -> u32 {
        let mut offset = 0;
        for ty in &self.tys {
            let sz = ty.size();
            let aln = ty.align();
            offset = align(offset, aln);
            offset += sz;
        }
        align(offset, 16)
    }

    pub fn offset_of(&self, idx: u32) -> u32 {
        let mut offset = 0;
        for ty in &self.tys[..idx as usize] {
            let sz = ty.size();
            let aln = ty.align();
            offset = align(offset, aln);
            offset += sz;
        }
        align(offset, self.tys[idx as usize].align())
    }

    pub fn iter<'a>(&'a self) -> iter::Cloned<slice::Iter<'a, Type<'ctx>>> {
        self.tys.iter().cloned()
    }

    pub fn get(&self, idx: u32) -> Option<Type<'ctx>> {
        self.tys.get(idx as usize).map(|&x| x)
    }
}

impl<'ctx> Index<u32> for TypeList<'ctx> {
    type Output = Type<'ctx>;
    fn index(&self, idx: u32) -> &Type<'ctx> {
        &self.tys[idx as usize]
    }
}

impl<'a, 'ctx> IntoIterator for &'a TypeList<'ctx> {
    type Item = Type<'ctx>;
    type IntoIter = iter::Cloned<slice::Iter<'a, Type<'ctx>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.tys.iter().cloned()
    }
}
