// TODO(ubsan): make sure to start dealing with Spanneds
// whee errors are fun
// TODO(ubsan): typeck should *probably* be done in AST
// the current typeck is pretty hax
// TODO(ubsan): figure out a good way to give params names
// without lots of allocations

mod runner;
mod ty;
mod data;

use ast::Ast;
use containers::Arena;
use parse::{Location, Spanned};

use self::runner::Runner;
pub use self::ty::*;
pub use self::data::*;

use std::ops::{Add, Rem, Sub};

#[inline(always)]
fn align<T>(x: T, to: T) -> T
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Rem<Output = T> + PartialEq,
{
    if to == x - x {
        x
    } else if x % to == x - x {
        x
    } else {
        x + (to - x % to)
    }
}

impl BlockData {
    fn new() -> Self {
        BlockData {
            stmts: vec![],
            term: Terminator::Return,
        }
    }

    fn with_term(term: Terminator) -> Self {
        BlockData {
            stmts: vec![],
            term,
        }
    }
}

#[derive(Debug)]
struct FunctionValue<'ctx> {
    // NOTE(ubsan): *this is just for stack locals, not for args*
    locals: TypeList<'ctx>,
    blks: Vec<BlockData>,
    bindings: Vec<Binding<'ctx>>,
}

#[derive(Debug)]
pub struct FunctionBuilder<'ctx> {
    decl: FunctionDecl,
    locals: TypeList<'ctx>,
    blks: Vec<BlockData>,
    bindings: Vec<Binding<'ctx>>,
}

// creation and misc
impl<'ctx> FunctionBuilder<'ctx> {
    fn new(decl: FunctionDecl, mir: &Mir<'ctx>) -> Self {
        let enter_block = BlockData {
            stmts: vec![],
            term: Terminator::Goto(Block(1)),
        };
        let exit_block = BlockData {
            stmts: vec![],
            term: Terminator::Return,
        };

        let mut bindings = Vec::with_capacity(mir.funcs[decl.0].ty.params.tys.len() + 1);
        bindings.push(Binding {
            name: Some("<return>".to_owned()),
            ty: mir.funcs[decl.0].ty.ret,
            kind: BindingKind::Return,
        });
        for (i, ty) in mir.funcs[decl.0].ty.params.iter().enumerate() {
            bindings.push(Binding {
                name: None,
                ty,
                kind: BindingKind::Param(i as u32),
            })
        }
        FunctionBuilder {
            decl,
            locals: TypeList::new(),
            bindings,
            blks: vec![enter_block, exit_block],
        }
    }

    pub fn entrance(&self) -> Block {
        Block(0)
    }

    pub fn get_param(&self, n: u32) -> Reference {
        Reference::param(n)
    }
}

// modification
impl<'ctx> FunctionBuilder<'ctx> {
    pub fn add_stmt(
        &mut self,
        mir: &Mir<'ctx>,
        blk: Block,
        lhs: Reference,
        rhs: Value,
        start: Location,
        end: Option<Location>,
    ) -> Result<(), TypeError<'ctx>> {
        {
            let ty_lhs = self.bindings[lhs.0 as usize].ty;
            let ty_rhs = rhs.ty(self, mir, start, end)?;
            if ty_lhs != ty_rhs {
                return Err(Spanned {
                    thing: TypeErrorVariant::Mismatched {
                        lhs: ty_lhs,
                        rhs: ty_rhs,
                    },
                    start,
                    end,
                });
            }
        }
        let blk_data = &mut self.blks[blk.0 as usize];
        blk_data.stmts.push(Statement { lhs, rhs });
        Ok(())
    }

    // NOTE(ubsan): the returned blocks initially have
    // the same terminator as their parent
    pub fn term_if_else(&mut self, blk: Block, cond: Reference) -> (Block, Block, Block) {
        let (then, els, final_bb) = {
            let term = self.blks[blk.0 as usize].term;
            self.blks.push(BlockData::new());
            self.blks.push(BlockData::new());
            self.blks.push(BlockData::with_term(term));
            let len = self.blks.len();

            let final_bb = Block((len - 1) as u32);
            self.blks[len - 3].term = Terminator::Goto(final_bb);
            self.blks[len - 2].term = Terminator::Goto(final_bb);

            (Block((len - 3) as u32), Block((len - 2) as u32), final_bb)
        };

        self.blks[blk.0 as usize].term = Terminator::IfElse { cond, then, els };
        (then, els, final_bb)
    }

    pub fn add_anonymous_local(&mut self, ty: Type<'ctx>) -> Reference {
        self.locals.push(ty);
        let kind = BindingKind::Local((self.locals.tys.len() - 1) as u32);
        self.bindings.push(Binding {
            name: None,
            ty,
            kind,
        });
        Reference((self.bindings.len() - 1) as u32)
    }

    pub fn add_local(&mut self, name: String, ty: Type<'ctx>) -> Reference {
        self.locals.push(ty);
        let kind = BindingKind::Local((self.locals.tys.len() - 1) as u32);
        self.bindings.push(Binding {
            name: Some(name),
            ty,
            kind,
        });
        Reference((self.bindings.len() - 1) as u32)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct FunctionDecl(usize);

// NOTE(ubsan): when I get namespacing, I should probably
// use paths instead of names?

#[derive(Debug)]
pub struct FunctionType<'ctx> {
    pub params: TypeList<'ctx>,
    pub ret: Type<'ctx>,
}

struct Function<'ctx> {
    ty: FunctionType<'ctx>,
    name: Option<String>,
    value: Option<FunctionValue<'ctx>>,
}

pub struct MirCtxt<'a> {
    types: Arena<NamedType<'a>>,
}

impl<'a> MirCtxt<'a> {
    pub fn new() -> Self {
        MirCtxt {
            types: Arena::new(),
        }
    }
}

pub struct Mir<'ctx> {
    funcs: Vec<Function<'ctx>>,
    types: &'ctx Arena<NamedType<'ctx>>,
    builtin_types: BuiltinTypes<'ctx>,
}

// creation and run
impl<'ctx> Mir<'ctx> {
    pub fn new(ctx: &'ctx MirCtxt<'ctx>, mut ast: Ast) -> Result<Self, TypeError<'ctx>> {
        let types = &ctx.types;
        let builtin_types = BuiltinTypes {
            unit_ty: Type(types.push(NamedType::unit())),
            bool_ty: Type(types.push(NamedType::bool())),
            s32_ty: Type(types.push(NamedType::s32())),
        };
        let mut self_: Mir<'ctx> = Mir {
            funcs: vec![],
            types,
            builtin_types,
        };

        ast.build_mir(&mut self_)?;

        Ok(self_)
    }

    pub fn run(&self) -> i32 {
        for (i, &Function { ref name, .. }) in self.funcs.iter().enumerate() {
            if let Some("main") = name.as_ref().map(|s| &**s) {
                return Runner::new(self).run(FunctionDecl(i));
            }
        }
        panic!("no main function found")
    }
}

// functions
impl<'ctx> Mir<'ctx> {
    pub fn add_function_decl(
        &mut self,
        name: Option<String>,
        ty: FunctionType<'ctx>,
    ) -> FunctionDecl {
        self.funcs.push(Function {
            ty,
            name,
            value: None,
        });
        FunctionDecl(self.funcs.len() - 1)
    }

    pub fn get_function_builder(&self, decl: FunctionDecl) -> FunctionBuilder<'ctx> {
        FunctionBuilder::new(decl, self)
    }

    pub fn add_function_definition(&mut self, builder: FunctionBuilder<'ctx>) {
        let value = FunctionValue {
            blks: builder.blks,
            locals: builder.locals,
            bindings: builder.bindings,
        };

        self.funcs[builder.decl.0].value = Some(value);
    }
}

// types
impl<'ctx> Mir<'ctx> {
    /*
    pub fn insert_type(&self, ty: TypeVariant<'ctx>) -> Type<'ctx> {
        Type(self.types.push(ty))
    }
    */

    pub fn get_function_type(&self, decl: FunctionDecl) -> &FunctionType<'ctx> {
        &self.funcs[decl.0].ty
    }

    pub fn get_builtin_type(&self, ty: BuiltinType) -> Type<'ctx> {
        match ty {
            BuiltinType::Unit => self.builtin_types.unit_ty,
            BuiltinType::Bool => self.builtin_types.bool_ty,
            BuiltinType::SInt(IntSize::I32) => self.builtin_types.s32_ty,
        }
    }
}

// printing
impl<'ctx> Mir<'ctx> {
    pub fn print(&self) {
        fn binding_name(binding: &Option<String>) -> &str {
            binding.as_ref().map(|s| &**s).unwrap_or("")
        }
        fn print_binding(bindings: &[Binding], r: Reference) {
            let name = binding_name(&bindings[r.0 as usize].name);
            print!("{}_{}", name, r.0);
        }

        self.types.call_on_all(|&NamedType { ref ty, ref name }| {
            print!("type {} = ", name);
            match *ty {
                TypeVariant::Builtin(_) => {
                    println!("<builtin>;");
                }
                TypeVariant::__LifetimeHolder(_) => unreachable!(),
            }
        });
        for &Function {
            ref ty,
            ref name,
            ref value,
        } in &self.funcs
        {
            let (name, value) = (name.as_ref().unwrap(), value.as_ref().unwrap());
            print!("func {}(", name);
            if !ty.params.tys.is_empty() {
                let tys = &ty.params.tys;
                for par in &tys[..tys.len() - 1] {
                    print!("{}, ", par.name());
                }
                print!("{}", tys[tys.len() - 1].name());
            }
            println!("): {} = {{", ty.ret.name());

            println!("  locals = {{");
            for loc_ty in &value.locals {
                println!("    {},", loc_ty.name());
            }
            println!("  }}");

            println!("  bindings = {{");
            for (i, binding) in value.bindings.iter().enumerate() {
                match binding.kind {
                    BindingKind::Return => println!("    <return>: {},", binding.ty.name()),
                    BindingKind::Param(p) => {
                        println!(
                            "    {}_{}: {} = <params>[{}],",
                            binding_name(&binding.name),
                            i,
                            binding.ty.name(),
                            p,
                        );
                    }
                    BindingKind::Local(loc) => {
                        println!(
                            "    {}_{}: {} = <locals>[{}],",
                            binding_name(&binding.name),
                            i,
                            binding.ty.name(),
                            loc,
                        );
                    }
                }
            }
            println!("  }}");

            let print_value = |val: &Value| match *val {
                Value::Literal(ref n) => {
                    println!("literal {:?};", n);
                }
                Value::Negative(r) => {
                    print!("-");
                    print_binding(&value.bindings, r);
                    println!(";");
                }
                Value::Reference(r) => {
                    print_binding(&value.bindings, r);
                    println!(";");
                }
                Value::Add(lhs, rhs) => {
                    print_binding(&value.bindings, lhs);
                    print!(" + ");
                    print_binding(&value.bindings, rhs);
                    println!(";");
                }
                Value::LessEq(lhs, rhs) => {
                    print_binding(&value.bindings, lhs);
                    print!(" <= ");
                    print_binding(&value.bindings, rhs);
                    println!(";");
                }
                Value::Call {
                    ref callee,
                    ref args,
                } => {
                    let name = match self.funcs[callee.0].name {
                        Some(ref name) => &**name,
                        None => "<anonymous>",
                    };
                    print!("{}(", name);
                    if !args.is_empty() {
                        for arg in &args[..args.len() - 1] {
                            print_binding(&value.bindings, *arg);
                            print!(", ");
                        }
                        print_binding(&value.bindings, args[args.len() - 1]);
                    }
                    println!(");");
                }
                Value::Log(ref arg) => {
                    print!("log(");
                    print_binding(&value.bindings, *arg);
                    println!(");");
                }
            };

            for (n, bb) in value.blks.iter().enumerate() {
                println!("  bb{} = {{", n);
                for stmt in &bb.stmts {
                    let Statement { ref lhs, ref rhs } = *stmt;
                    if lhs.0 == 0 {
                        print!("    <return> = ");
                    } else {
                        print!("    ");
                        print_binding(&value.bindings, *lhs);
                        print!(" = ");
                    }
                    print_value(rhs);
                }
                match bb.term {
                    Terminator::Goto(blk) => {
                        println!("    goto bb{};", blk.0);
                    }
                    Terminator::Return => {
                        println!("    return;");
                    }
                    Terminator::IfElse { cond, then, els } => {
                        print!("    if ");
                        print_binding(&value.bindings, cond);
                        println!(" {{ bb{} }} else {{ bb{} }}", then.0, els.0,);
                    }
                }
                println!("  }}");
            }
            println!("}}");
        }
    }
}
