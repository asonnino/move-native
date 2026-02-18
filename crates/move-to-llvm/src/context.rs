use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::IntType;

/// Wraps the LLVM Context, Module, and Builder for a single compilation unit.
pub struct LlvmContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    // Cached integer types
    pub i8_type: IntType<'ctx>,
    pub i16_type: IntType<'ctx>,
    pub i32_type: IntType<'ctx>,
    pub i64_type: IntType<'ctx>,
    pub i128_type: IntType<'ctx>,
    pub i256_type: IntType<'ctx>,
}

impl<'ctx> LlvmContext<'ctx> {
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();

        Self {
            context,
            module,
            builder,
            i8_type: context.i8_type(),
            i16_type: context.i16_type(),
            i32_type: context.i32_type(),
            i64_type: context.i64_type(),
            i128_type: context.i128_type(),
            i256_type: context.custom_width_int_type(256),
        }
    }
}
