// Copyright 2021 Robin Freyler
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Utilities to translate a Wasm function body into a Runwell function body.

#![allow(unused_variables)]

mod error;
mod stack;

pub use self::error::TranslateError;
use self::stack::ValueStack;
use crate::{Error, Type};
use core::convert::TryFrom as _;
use entity::RawIdx;
use ir::{
    primitive as runwell,
    primitive::{FloatType, Func, IntConst, IntType},
};
use module::{FunctionBody, FunctionBuilder, ModuleResources};
use wasmparser::{BinaryReader, FuncValidator, Range, ValidatorResources};

/// Translate a Wasm function body into a Runwell function body.
///
/// # Note
///
/// - The `buffer` contains the binary encoded Wasm function body.
/// - The Wasm function body is parsed and validated during construction.
pub fn translate_function_body(
    range: Range,
    buffer: Vec<u8>,
    validator: FuncValidator<ValidatorResources>,
    func: Func,
    res: &ModuleResources,
) -> Result<FunctionBody, Error> {
    let wasm_body = wasmparser::FunctionBody::new(range.start, &buffer[..]);
    let function_body =
        FunctionBodyTranslator::new(wasm_body, validator, func, res)
            .translate()?;
    Ok(function_body)
}

/// Translates Wasm function bodies into Runwell function bodies.
pub struct FunctionBodyTranslator<'a, 'b> {
    // The Wasm function body.
    reader: BinaryReader<'a>,
    /// Used to validate a function on the fly during translation.
    validator: FuncValidator<ValidatorResources>,
    /// The unique function index associated to the translated function body.
    func: Func,
    /// The immutable module resources required to translate the function body.
    res: &'b ModuleResources,
    /// The Runwell function body builder.
    builder: FunctionBuilder,
    /// The emulated Wasm stack to translate the Wasm stack machine.
    stack: ValueStack,
}

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Creates a new Wasm to Runwell function body translator.
    fn new(
        wasm_body: wasmparser::FunctionBody<'a>,
        validator: FuncValidator<ValidatorResources>,
        func: Func,
        res: &'b ModuleResources,
    ) -> Self {
        let mut reader = wasm_body.get_binary_reader();
        let _body_size = reader
            .read_var_u32()
            .expect("expect function size in bytes");
        Self {
            reader,
            validator,
            func,
            res,
            builder: FunctionBody::build(),
            stack: Default::default(),
        }
    }

    /// Translates the Wasm function body into an equivalent Runwell function body.
    fn translate(mut self) -> Result<FunctionBody, Error> {
        self.translate_inputs_outputs()?;
        self.translate_local_variables()?;
        self.translate_operators()?;
        let body = self.builder.finalize()?;
        Ok(body)
    }

    /// Populates the constructed Runwell function with input and output types.
    fn translate_inputs_outputs(&mut self) -> Result<(), Error> {
        let func_type = self
            .res
            .get_func_type(self.func)
            .expect("encountered invalid function reference");
        self.builder.with_inputs(func_type.inputs())?;
        self.builder.with_outputs(func_type.outputs())?;
        Ok(())
    }

    /// Parses, validates and translates the Wasm local variables into
    /// Runwell variable declarations.
    fn translate_local_variables(&mut self) -> Result<(), Error> {
        let count_locals = self.reader.read_var_u32()?;
        for _ in 0..count_locals {
            let offset = self.reader.original_position();
            let count = self.reader.read_var_u32()?;
            let ty = self.reader.read_type()?;
            self.validator.define_locals(offset, count, ty)?;
            let ty = Type::try_from(ty)?.into_inner();
            self.builder.declare_variables(count, ty)?;
        }
        Ok(())
    }

    /// Parses, validates and translates the Wasm operands into Runwell
    /// function body instructions and basic blocks.
    fn translate_operators(&mut self) -> Result<(), Error> {
        while !self.reader.eof() {
            let offset = self.reader.original_position();
            let op = self.reader.read_operator()?;
            self.validator.op(offset, &op)?;
            self.translate_operator(offset, op)?;
        }
        let offset = self.reader.original_position();
        self.validator.finish(offset)?;
        Ok(())
    }

    /// Translate a single Wasm operand into Runwell IR.
    fn translate_operator(
        &mut self,
        offset: usize,
        op: wasmparser::Operator,
    ) -> Result<(), Error> {
        use wasmparser::Operator as Op;
        match op {
            Op::Unreachable => {
                self.builder.ins()?.trap()?;
            }
            Op::Nop => {}
            Op::Block { ty } => {}
            Op::Loop { ty } => {}
            Op::If { ty } => {}
            Op::Else => {}
            Op::End => {}
            Op::Br { relative_depth } => {}
            Op::BrIf { relative_depth } => {}
            Op::BrTable { table } => {}
            Op::Return => {}
            Op::Call { function_index } => {
                let func = Func::from_raw(RawIdx::from_u32(function_index));
                let func_type = self
                    .res
                    .get_func_type(func)
                    .expect("function type must exist due to validation");
                let params = self
                    .stack
                    .pop_n(func_type.inputs().len())?
                    .map(|entry| entry.value);
                let result = self.builder.ins()?.call(func, params)?;
                for output_type in func_type.outputs() {
                    self.stack.push(result, *output_type);
                }
            }
            Op::CallIndirect { index, table_index } => {}
            Op::ReturnCall { function_index } => {}
            Op::ReturnCallIndirect { index, table_index } => {}
            Op::Drop => {
                self.stack.pop1()?;
            }
            Op::Select => {
                self.translate_select_operator(None)?;
            }
            Op::TypedSelect { ty } => {
                let ty = Type::try_from(ty)?.into_inner();
                self.translate_select_operator(Some(ty))?;
            }
            Op::LocalGet { local_index } => {
                // let var = Variable::from_raw(RawIdx::from_u32(local_index));
                // let result = self.builder.read_var(var)?;
            }
            Op::LocalSet { local_index } => {}
            Op::LocalTee { local_index } => {}
            Op::GlobalGet { global_index } => {}
            Op::GlobalSet { global_index } => {}
            Op::I32Load { memarg } => {}
            Op::I64Load { memarg } => {}
            Op::F32Load { memarg } => {}
            Op::F64Load { memarg } => {}
            Op::I32Load8S { memarg } => {}
            Op::I32Load8U { memarg } => {}
            Op::I32Load16S { memarg } => {}
            Op::I32Load16U { memarg } => {}
            Op::I64Load8S { memarg } => {}
            Op::I64Load8U { memarg } => {}
            Op::I64Load16S { memarg } => {}
            Op::I64Load16U { memarg } => {}
            Op::I64Load32S { memarg } => {}
            Op::I64Load32U { memarg } => {}
            Op::I32Store { memarg } => {}
            Op::I64Store { memarg } => {}
            Op::F32Store { memarg } => {}
            Op::F64Store { memarg } => {}
            Op::I32Store8 { memarg } => {}
            Op::I32Store16 { memarg } => {}
            Op::I64Store8 { memarg } => {}
            Op::I64Store16 { memarg } => {}
            Op::I64Store32 { memarg } => {}
            Op::MemorySize { mem, mem_byte } => {}
            Op::MemoryGrow { mem, mem_byte } => {}
            Op::I32Const { value } => {
                let result = self.builder.ins()?.constant(
                    ir::primitive::Const::Int(IntConst::I32(value)),
                )?;
                self.stack.push(result, IntType::I32.into());
            }
            Op::I64Const { value } => {
                let result = self.builder.ins()?.constant(
                    ir::primitive::Const::Int(IntConst::I64(value)),
                )?;
                self.stack.push(result, IntType::I64.into());
            }
            Op::F32Const { value } => {
                let value = crate::Value::from(value).into_inner();
                let result = self.builder.ins()?.constant(value)?;
                self.stack.push(result, FloatType::F32.into());
            }
            Op::F64Const { value } => {
                let value = crate::Value::from(value).into_inner();
                let result = self.builder.ins()?.constant(value)?;
                self.stack.push(result, FloatType::F64.into());
            }
            Op::I32Eqz => {}
            Op::I32Eq => {}
            Op::I32Ne => {}
            Op::I32LtS => {}
            Op::I32LtU => {}
            Op::I32GtS => {}
            Op::I32GtU => {}
            Op::I32LeS => {}
            Op::I32LeU => {}
            Op::I32GeS => {}
            Op::I32GeU => {}
            Op::I64Eqz => {}
            Op::I64Eq => {}
            Op::I64Ne => {}
            Op::I64LtS => {}
            Op::I64LtU => {}
            Op::I64GtS => {}
            Op::I64GtU => {}
            Op::I64LeS => {}
            Op::I64LeU => {}
            Op::I64GeS => {}
            Op::I64GeU => {}
            Op::F32Eq => {}
            Op::F32Ne => {}
            Op::F32Lt => {}
            Op::F32Gt => {}
            Op::F32Le => {}
            Op::F32Ge => {}
            Op::F64Eq => {}
            Op::F64Ne => {}
            Op::F64Lt => {}
            Op::F64Gt => {}
            Op::F64Le => {}
            Op::F64Ge => {}
            Op::I32Clz => {}
            Op::I32Ctz => {}
            Op::I32Popcnt => {}
            Op::I32Add => {}
            Op::I32Sub => {}
            Op::I32Mul => {}
            Op::I32DivS => {}
            Op::I32DivU => {}
            Op::I32RemS => {}
            Op::I32RemU => {}
            Op::I32And => {}
            Op::I32Or => {}
            Op::I32Xor => {}
            Op::I32Shl => {}
            Op::I32ShrS => {}
            Op::I32ShrU => {}
            Op::I32Rotl => {}
            Op::I32Rotr => {}
            Op::I64Clz => {}
            Op::I64Ctz => {}
            Op::I64Popcnt => {}
            Op::I64Add => {}
            Op::I64Sub => {}
            Op::I64Mul => {}
            Op::I64DivS => {}
            Op::I64DivU => {}
            Op::I64RemS => {}
            Op::I64RemU => {}
            Op::I64And => {}
            Op::I64Or => {}
            Op::I64Xor => {}
            Op::I64Shl => {}
            Op::I64ShrS => {}
            Op::I64ShrU => {}
            Op::I64Rotl => {}
            Op::I64Rotr => {}
            Op::F32Abs => {}
            Op::F32Neg => {}
            Op::F32Ceil => {}
            Op::F32Floor => {}
            Op::F32Trunc => {}
            Op::F32Nearest => {}
            Op::F32Sqrt => {}
            Op::F32Add => {}
            Op::F32Sub => {}
            Op::F32Mul => {}
            Op::F32Div => {}
            Op::F32Min => {}
            Op::F32Max => {}
            Op::F32Copysign => {}
            Op::F64Abs => {}
            Op::F64Neg => {}
            Op::F64Ceil => {}
            Op::F64Floor => {}
            Op::F64Trunc => {}
            Op::F64Nearest => {}
            Op::F64Sqrt => {}
            Op::F64Add => {}
            Op::F64Sub => {}
            Op::F64Mul => {}
            Op::F64Div => {}
            Op::F64Min => {}
            Op::F64Max => {}
            Op::F64Copysign => {}
            Op::I32WrapI64 => {}
            Op::I32TruncF32S => {}
            Op::I32TruncF32U => {}
            Op::I32TruncF64S => {}
            Op::I32TruncF64U => {}
            Op::I64ExtendI32S => {}
            Op::I64ExtendI32U => {}
            Op::I64TruncF32S => {}
            Op::I64TruncF32U => {}
            Op::I64TruncF64S => {}
            Op::I64TruncF64U => {}
            Op::F32ConvertI32S => {}
            Op::F32ConvertI32U => {}
            Op::F32ConvertI64S => {}
            Op::F32ConvertI64U => {}
            Op::F32DemoteF64 => {}
            Op::F64ConvertI32S => {}
            Op::F64ConvertI32U => {}
            Op::F64ConvertI64S => {}
            Op::F64ConvertI64U => {}
            Op::F64PromoteF32 => {}
            Op::I32ReinterpretF32 => {}
            Op::I64ReinterpretF64 => {}
            Op::F32ReinterpretI32 => {}
            Op::F64ReinterpretI64 => {}
            Op::I32Extend8S => {}
            Op::I32Extend16S => {}
            Op::I64Extend8S => {}
            Op::I64Extend16S => {}
            Op::I64Extend32S => {}

            _unsupported => {
                return Err(TranslateError::UnsupportedOperator { offset })
                    .map_err(Into::into)
            }
        }
        Ok(())
    }

    /// Translates a Wasm `Select` or `TypedSelect` operator.
    fn translate_select_operator(
        &mut self,
        required_ty: Option<runwell::Type>,
    ) -> Result<(), Error> {
        let (condition, if_true, if_false) = self.stack.pop3()?;
        assert_eq!(
            if_true.ty, if_false.ty,
            "due to validation both types must be equal"
        );
        if let Some(required_ty) = required_ty {
            assert_eq!(if_true.ty, required_ty);
        }
        let ty = if_true.ty;
        let result = self.builder.ins()?.select(
            ty,
            condition.value,
            if_true.value,
            if_false.value,
        )?;
        self.stack.push(result, ty);
        Ok(())
    }
}
