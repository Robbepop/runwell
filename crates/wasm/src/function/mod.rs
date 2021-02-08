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
use crate::{Const as WasmConst, Error, Type};
use core::convert::TryFrom as _;
use entity::RawIdx;
use ir::{
    instr::operands::{
        BinaryFloatOp,
        BinaryIntOp,
        CompareFloatOp,
        CompareIntOp,
        ShiftIntOp,
        UnaryFloatOp,
        UnaryIntOp,
    },
    primitive as runwell,
    primitive::{FloatType, Func, IntConst, IntType},
};
use module::{FunctionBody, FunctionBuilder, ModuleResources, Variable};
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
        use BinaryFloatOp as BinFloatOp;
        use CompareFloatOp as CmpFloatOp;
        use CompareIntOp as CmpIntOp;
        use FloatType::{F32, F64};
        use IntType::{I32, I64};
        use UnaryFloatOp as FloatUnop;
        use UnaryIntOp::*;
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
                self.translate_call(function_index)?
            }
            Op::CallIndirect { index, table_index } => {}
            Op::ReturnCall { function_index } => {}
            Op::ReturnCallIndirect { index, table_index } => {}
            Op::Drop => {
                self.stack.pop1()?;
            }
            Op::Select => {
                self.translate_select_op(None)?;
            }
            Op::TypedSelect { ty } => {
                let ty = Type::try_from(ty)?.into_inner();
                self.translate_select_op(Some(ty))?;
            }
            Op::LocalGet { local_index } => {
                self.translate_local_get(local_index)?
            }
            Op::LocalSet { local_index } => {
                self.translate_local_set(local_index)?
            }
            Op::LocalTee { local_index } => {
                self.translate_local_tee(local_index)?
            }
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
            Op::I32Const { value } => self.translate_const_op(value, I32)?,
            Op::I64Const { value } => self.translate_const_op(value, I64)?,
            Op::F32Const { value } => self.translate_const_op(value, F32)?,
            Op::F64Const { value } => self.translate_const_op(value, F64)?,
            Op::I32Eqz => self.translate_eqz_op(IntType::I32)?,
            Op::I32Eq => self.translate_icmp_op(CmpIntOp::Eq, I32)?,
            Op::I32Ne => self.translate_icmp_op(CmpIntOp::Ne, I32)?,
            Op::I32LtS => self.translate_icmp_op(CmpIntOp::Slt, I32)?,
            Op::I32LtU => self.translate_icmp_op(CmpIntOp::Ult, I32)?,
            Op::I32GtS => self.translate_icmp_op(CmpIntOp::Sgt, I32)?,
            Op::I32GtU => self.translate_icmp_op(CmpIntOp::Ugt, I32)?,
            Op::I32LeS => self.translate_icmp_op(CmpIntOp::Sle, I32)?,
            Op::I32LeU => self.translate_icmp_op(CmpIntOp::Ule, I32)?,
            Op::I32GeS => self.translate_icmp_op(CmpIntOp::Sge, I32)?,
            Op::I32GeU => self.translate_icmp_op(CmpIntOp::Uge, I32)?,
            Op::I64Eqz => self.translate_eqz_op(IntType::I64)?,
            Op::I64Eq => self.translate_icmp_op(CmpIntOp::Eq, I64)?,
            Op::I64Ne => self.translate_icmp_op(CmpIntOp::Ne, I64)?,
            Op::I64LtS => self.translate_icmp_op(CmpIntOp::Slt, I64)?,
            Op::I64LtU => self.translate_icmp_op(CmpIntOp::Ult, I64)?,
            Op::I64GtS => self.translate_icmp_op(CmpIntOp::Sgt, I64)?,
            Op::I64GtU => self.translate_icmp_op(CmpIntOp::Ugt, I64)?,
            Op::I64LeS => self.translate_icmp_op(CmpIntOp::Sle, I64)?,
            Op::I64LeU => self.translate_icmp_op(CmpIntOp::Ule, I64)?,
            Op::I64GeS => self.translate_icmp_op(CmpIntOp::Sge, I64)?,
            Op::I64GeU => self.translate_icmp_op(CmpIntOp::Uge, I64)?,
            Op::F32Eq => self.translate_fcmp_op(CmpFloatOp::Eq, F32)?,
            Op::F32Ne => self.translate_fcmp_op(CmpFloatOp::Ne, F32)?,
            Op::F32Lt => self.translate_fcmp_op(CmpFloatOp::Lt, F32)?,
            Op::F32Gt => self.translate_fcmp_op(CmpFloatOp::Gt, F32)?,
            Op::F32Le => self.translate_fcmp_op(CmpFloatOp::Le, F32)?,
            Op::F32Ge => self.translate_fcmp_op(CmpFloatOp::Lt, F32)?,
            Op::F64Eq => self.translate_fcmp_op(CmpFloatOp::Eq, F64)?,
            Op::F64Ne => self.translate_fcmp_op(CmpFloatOp::Ne, F64)?,
            Op::F64Lt => self.translate_fcmp_op(CmpFloatOp::Lt, F64)?,
            Op::F64Gt => self.translate_fcmp_op(CmpFloatOp::Gt, F64)?,
            Op::F64Le => self.translate_fcmp_op(CmpFloatOp::Le, F64)?,
            Op::F64Ge => self.translate_fcmp_op(CmpFloatOp::Ge, F64)?,
            Op::I32Clz => self.translate_int_unop(I32, LeadingZeros)?,
            Op::I32Ctz => self.translate_int_unop(I32, TrailingZeros)?,
            Op::I32Popcnt => self.translate_int_unop(I32, PopCount)?,
            Op::I32Add => self.translate_int_binop(I32, BinaryIntOp::Add)?,
            Op::I32Sub => self.translate_int_binop(I32, BinaryIntOp::Sub)?,
            Op::I32Mul => self.translate_int_binop(I32, BinaryIntOp::Mul)?,
            Op::I32DivS => self.translate_int_binop(I32, BinaryIntOp::Sdiv)?,
            Op::I32DivU => self.translate_int_binop(I32, BinaryIntOp::Udiv)?,
            Op::I32RemS => self.translate_int_binop(I32, BinaryIntOp::Srem)?,
            Op::I32RemU => self.translate_int_binop(I32, BinaryIntOp::Urem)?,
            Op::I32And => self.translate_int_binop(I32, BinaryIntOp::And)?,
            Op::I32Or => self.translate_int_binop(I32, BinaryIntOp::Or)?,
            Op::I32Xor => self.translate_int_binop(I32, BinaryIntOp::Xor)?,
            Op::I32Shl => self.translate_int_shift(I32, ShiftIntOp::Shl)?,
            Op::I32ShrS => self.translate_int_shift(I32, ShiftIntOp::Sshr)?,
            Op::I32ShrU => self.translate_int_shift(I32, ShiftIntOp::Ushr)?,
            Op::I32Rotl => self.translate_int_shift(I32, ShiftIntOp::Rotl)?,
            Op::I32Rotr => self.translate_int_shift(I32, ShiftIntOp::Rotr)?,
            Op::I64Clz => self.translate_int_unop(I64, LeadingZeros)?,
            Op::I64Ctz => self.translate_int_unop(I64, TrailingZeros)?,
            Op::I64Popcnt => self.translate_int_unop(I64, PopCount)?,
            Op::I64Add => self.translate_int_binop(I64, BinaryIntOp::Add)?,
            Op::I64Sub => self.translate_int_binop(I64, BinaryIntOp::Sub)?,
            Op::I64Mul => self.translate_int_binop(I64, BinaryIntOp::Mul)?,
            Op::I64DivS => self.translate_int_binop(I64, BinaryIntOp::Sdiv)?,
            Op::I64DivU => self.translate_int_binop(I64, BinaryIntOp::Udiv)?,
            Op::I64RemS => self.translate_int_binop(I64, BinaryIntOp::Srem)?,
            Op::I64RemU => self.translate_int_binop(I64, BinaryIntOp::Urem)?,
            Op::I64And => self.translate_int_binop(I64, BinaryIntOp::And)?,
            Op::I64Or => self.translate_int_binop(I64, BinaryIntOp::Or)?,
            Op::I64Xor => self.translate_int_binop(I64, BinaryIntOp::Xor)?,
            Op::I64Shl => self.translate_int_shift(I64, ShiftIntOp::Shl)?,
            Op::I64ShrS => self.translate_int_shift(I64, ShiftIntOp::Sshr)?,
            Op::I64ShrU => self.translate_int_shift(I64, ShiftIntOp::Ushr)?,
            Op::I64Rotl => self.translate_int_shift(I64, ShiftIntOp::Rotl)?,
            Op::I64Rotr => self.translate_int_shift(I64, ShiftIntOp::Rotr)?,
            Op::F32Abs => self.translate_float_unop(F32, FloatUnop::Abs)?,
            Op::F32Neg => self.translate_float_unop(F32, FloatUnop::Neg)?,
            Op::F32Ceil => self.translate_float_unop(F32, FloatUnop::Ceil)?,
            Op::F32Floor => self.translate_float_unop(F32, FloatUnop::Floor)?,
            Op::F32Trunc => {
                self.translate_float_unop(F32, FloatUnop::Truncate)?
            }
            Op::F32Nearest => {
                self.translate_float_unop(F32, FloatUnop::Nearest)?
            }
            Op::F32Sqrt => self.translate_float_unop(F32, FloatUnop::Sqrt)?,
            Op::F32Add => self.translate_float_binop(F32, BinFloatOp::Add)?,
            Op::F32Sub => self.translate_float_binop(F32, BinFloatOp::Sub)?,
            Op::F32Mul => self.translate_float_binop(F32, BinFloatOp::Mul)?,
            Op::F32Div => self.translate_float_binop(F32, BinFloatOp::Div)?,
            Op::F32Min => self.translate_float_binop(F32, BinFloatOp::Min)?,
            Op::F32Max => self.translate_float_binop(F32, BinFloatOp::Max)?,
            Op::F32Copysign => {
                self.translate_float_binop(F32, BinFloatOp::CopySign)?
            }
            Op::F64Abs => self.translate_float_unop(F64, FloatUnop::Abs)?,
            Op::F64Neg => self.translate_float_unop(F64, FloatUnop::Neg)?,
            Op::F64Ceil => self.translate_float_unop(F64, FloatUnop::Ceil)?,
            Op::F64Floor => self.translate_float_unop(F64, FloatUnop::Floor)?,
            Op::F64Trunc => {
                self.translate_float_unop(F64, FloatUnop::Truncate)?
            }
            Op::F64Nearest => {
                self.translate_float_unop(F64, FloatUnop::Nearest)?
            }
            Op::F64Sqrt => self.translate_float_unop(F64, FloatUnop::Sqrt)?,
            Op::F64Add => self.translate_float_binop(F64, BinFloatOp::Add)?,
            Op::F64Sub => self.translate_float_binop(F64, BinFloatOp::Sub)?,
            Op::F64Mul => self.translate_float_binop(F64, BinFloatOp::Mul)?,
            Op::F64Div => self.translate_float_binop(F64, BinFloatOp::Div)?,
            Op::F64Min => self.translate_float_binop(F64, BinFloatOp::Min)?,
            Op::F64Max => self.translate_float_binop(F64, BinFloatOp::Max)?,
            Op::F64Copysign => {
                self.translate_float_binop(F64, BinFloatOp::CopySign)?
            }
            Op::I32TruncF32S => self.translate_float_to_sint(F32, I32)?,
            Op::I32TruncF32U => self.translate_float_to_uint(F32, I32)?,
            Op::I32TruncF64S => self.translate_float_to_sint(F64, I32)?,
            Op::I32TruncF64U => self.translate_float_to_uint(F64, I32)?,
            Op::I64TruncF32S => self.translate_float_to_sint(F32, I64)?,
            Op::I64TruncF32U => self.translate_float_to_uint(F32, I64)?,
            Op::I64TruncF64S => self.translate_float_to_sint(F64, I64)?,
            Op::I64TruncF64U => self.translate_float_to_uint(F64, I64)?,
            Op::I32TruncSatF32S => self.translate_float_to_sint_sat(F32, I32)?,
            Op::I32TruncSatF32U => self.translate_float_to_uint_sat(F32, I32)?,
            Op::I32TruncSatF64S => self.translate_float_to_sint_sat(F64, I32)?,
            Op::I32TruncSatF64U => self.translate_float_to_uint_sat(F64, I32)?,
            Op::I64TruncSatF32S => self.translate_float_to_sint_sat(F32, I64)?,
            Op::I64TruncSatF32U => self.translate_float_to_uint_sat(F32, I64)?,
            Op::I64TruncSatF64S => self.translate_float_to_sint_sat(F64, I64)?,
            Op::I64TruncSatF64U => self.translate_float_to_uint_sat(F64, I64)?,
            Op::F32ConvertI32S => self.translate_int_to_float(I32, F32, true)?,
            Op::F32ConvertI32U => self.translate_int_to_float(I32, F32, false)?,
            Op::F32ConvertI64S => self.translate_int_to_float(I64, F32, true)?,
            Op::F32ConvertI64U => self.translate_int_to_float(I64, F32, false)?,
            Op::F64ConvertI32S => self.translate_int_to_float(I32, F64, true)?,
            Op::F64ConvertI32U => self.translate_int_to_float(I32, F64, false)?,
            Op::F64ConvertI64S => self.translate_int_to_float(I64, F64, true)?,
            Op::F64ConvertI64U => self.translate_int_to_float(I64, F64, false)?,
            Op::F32DemoteF64 => self.translate_demote(F64, F32)?,
            Op::F64PromoteF32 => self.translate_promote(F32, F64)?,
            Op::I32ReinterpretF32 => self.translate_reinterpret(I32, F32)?,
            Op::I64ReinterpretF64 => self.translate_reinterpret(I64, F64)?,
            Op::F32ReinterpretI32 => self.translate_reinterpret(F32, F32)?,
            Op::F64ReinterpretI64 => self.translate_reinterpret(F64, I64)?,
            Op::I32WrapI64 => self.translate_truncate(I64, I32)?,
            Op::I64ExtendI32S => self.translate_extend(I32, I64, true)?,
            Op::I64ExtendI32U => self.translate_extend(I32, I64, false)?,
            Op::I32Extend8S => {
                self.translate_truncate(I32, I8)?;
                self.translate_extend(I8, I32, true)?;
            }
            Op::I32Extend16S => {
                self.translate_truncate(I32, I16)?;
                self.translate_extend(I16, I32, true)?;
            }
            Op::I64Extend8S => {
                self.translate_truncate(I64, I8)?;
                self.translate_extend(I8, I64, true)?;
            }
            Op::I64Extend16S => {
                self.translate_truncate(I64, I16)?;
                self.translate_extend(I16, I64, true)?;
            }
            Op::I64Extend32S => {
                self.translate_truncate(I64, I32)?;
                self.translate_extend(I32, I64, true)?;
            }

            _unsupported => {
                return Err(TranslateError::UnsupportedOperator { offset })
                    .map_err(Into::into)
            }
        }
        Ok(())
    }

    /// Translates a Wasm function call.
    fn translate_call(&mut self, function_index: u32) -> Result<(), Error> {
        let func = Func::from_raw(RawIdx::from_u32(function_index));
        let func_type = self.res.get_func_type(func).unwrap_or_else(|| {
            panic!("function type for {} must exist due to validation", func)
        });
        let len_inputs = func_type.inputs().len();
        let params = self
            .stack
            .pop_n(len_inputs)
            .unwrap_or_else(|_| {
                panic!(
                    "can expect {} arguments on the stack due to validation",
                    len_inputs
                )
            })
            .map(|entry| entry.value);
        let result = self.builder.ins()?.call(func, params)?;
        for output_type in func_type.outputs() {
            self.stack.push(result, *output_type);
        }
        Ok(())
    }

    /// Translates Wasm `local_get` operator.
    fn translate_local_get(&mut self, local_index: u32) -> Result<(), Error> {
        let var = Variable::from_raw(RawIdx::from_u32(local_index));
        let result = self.builder.read_var(var)?;
        let result_type = self.builder.var_type(var)?;
        self.stack.push(result, result_type);
        Ok(())
    }

    /// Translates Wasm `local_set` operator.
    fn translate_local_set(&mut self, local_index: u32) -> Result<(), Error> {
        let var = Variable::from_raw(RawIdx::from_u32(local_index));
        let source = self.stack.pop1()?;
        self.builder.write_var(var, source.value)?;
        Ok(())
    }

    /// Translates Wasm `local_tee` operator.
    fn translate_local_tee(&mut self, local_index: u32) -> Result<(), Error> {
        let var = Variable::from_raw(RawIdx::from_u32(local_index));
        let source = self.stack.peek1()?;
        self.builder.write_var(var, source.value)?;
        Ok(())
    }
    /// Translates a Wasm integer to float conversion.
    fn translate_int_to_float<SrcType, DstType>(

    /// Translates a Wasm integer extend operator.
    fn translate_extend<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
        src_signed: bool,
    ) -> Result<(), Error>
    where
        SrcType: Into<IntType>,
        DstType: Into<IntType>,
    {
        let src_type = src_type.into();
        let dst_type = dst_type.into();
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, src_type.into());
        let source = source.value;
        let result = self
            .builder
            .ins()?
            .iextend(src_type, dst_type, source, src_signed)?;
        self.stack.push(result, dst_type.into());
        Ok(())
    }

    /// Translates a Wasm integer truncate operator.
    fn translate_truncate<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
    ) -> Result<(), Error>
    where
        SrcType: Into<IntType>,
        DstType: Into<IntType>,
    {
        let src_type = src_type.into();
        let dst_type = dst_type.into();
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, src_type.into());
        let source = source.value;
        let result =
            self.builder.ins()?.itruncate(src_type, dst_type, source)?;
        self.stack.push(result, dst_type.into());
        Ok(())
    }

    /// Translates a Wasm integer to float conversion.
    fn translate_int_to_float<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
        src_signed: bool,
    ) -> Result<(), Error>
    where
        SrcType: Into<IntType>,
        DstType: Into<FloatType>,
    {
        let src_type = src_type.into();
        let dst_type = dst_type.into();
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, src_type.into());
        let source = source.value;
        let result = self
            .builder
            .ins()?
            .int_to_float(src_signed, src_type, dst_type, source)?;
        self.stack.push(result, dst_type.into());
        Ok(())
    }

    /// Translates a Wasm float to integer conversion.
    fn translate_float_to_int(
        &mut self,
        src_type: FloatType,
        dst_type: IntType,
        dst_signed: bool,
        saturating: bool,
    ) -> Result<(), Error> {
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, src_type.into());
        let source = source.value;
        let result = self
            .builder
            .ins()?
            .float_to_int(src_type, dst_type, dst_signed, source, saturating)?;
        self.stack.push(result, dst_type.into());
        Ok(())
    }

    /// Translates a Wasm float to integer conversion.
    fn translate_float_to_sint<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
    ) -> Result<(), Error>
    where
        SrcType: Into<FloatType>,
        DstType: Into<IntType>,
    {
        self.translate_float_to_int(
            src_type.into(),
            dst_type.into(),
            true,
            false,
        )
    }

    /// Translates a Wasm float to integer conversion.
    fn translate_float_to_sint_sat<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
    ) -> Result<(), Error>
    where
        SrcType: Into<FloatType>,
        DstType: Into<IntType>,
    {
        self.translate_float_to_int(
            src_type.into(),
            dst_type.into(),
            true,
            true,
        )
    }

    /// Translates a Wasm float to integer conversion.
    fn translate_float_to_uint<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
    ) -> Result<(), Error>
    where
        SrcType: Into<FloatType>,
        DstType: Into<IntType>,
    {
        self.translate_float_to_int(
            src_type.into(),
            dst_type.into(),
            false,
            false,
        )
    }

    /// Translates a Wasm float to integer conversion.
    fn translate_float_to_uint_sat<SrcType, DstType>(
        &mut self,
        src_type: SrcType,
        dst_type: DstType,
    ) -> Result<(), Error>
    where
        SrcType: Into<FloatType>,
        DstType: Into<IntType>,
    {
        self.translate_float_to_int(
            src_type.into(),
            dst_type.into(),
            false,
            true,
        )
    }

    /// Translates a Wasm demote operator.
    fn translate_demote<FromType, ToType>(
        &mut self,
        from_type: FromType,
        to_type: ToType,
    ) -> Result<(), Error>
    where
        FromType: Into<FloatType>,
        ToType: Into<FloatType>,
    {
        let from_type = from_type.into();
        let to_type = to_type.into();
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, from_type.into());
        let result =
            self.builder
                .ins()?
                .demote(from_type, to_type, source.value)?;
        self.stack.push(result, to_type.into());
        Ok(())
    }

    /// Translates a Wasm promote operator.
    fn translate_promote<FromType, ToType>(
        &mut self,
        from_type: FromType,
        to_type: ToType,
    ) -> Result<(), Error>
    where
        FromType: Into<FloatType>,
        ToType: Into<FloatType>,
    {
        let from_type = from_type.into();
        let to_type = to_type.into();
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, from_type.into());
        let result =
            self.builder
                .ins()?
                .promote(from_type, to_type, source.value)?;
        self.stack.push(result, to_type.into());
        Ok(())
    }

    /// Translates a Wasm reinterpret operator.
    fn translate_reinterpret<FromType, ToType>(
        &mut self,
        from_type: FromType,
        to_type: ToType,
    ) -> Result<(), Error>
    where
        FromType: Into<runwell::Type>,
        ToType: Into<runwell::Type>,
    {
        let from_type = from_type.into();
        let to_type = to_type.into();
        assert_eq!(from_type.bit_width(), to_type.bit_width());
        let source = self.stack.pop1()?;
        assert_eq!(source.ty, from_type);
        let result = self.builder.ins()?.reinterpret(
            from_type,
            to_type,
            source.value,
        )?;
        self.stack.push(result, to_type);
        Ok(())
    }

    /// Translates a Wasm constant operator.
    fn translate_const_op<T1, T2>(
        &mut self,
        const_value: T1,
        ty: T2,
    ) -> Result<(), Error>
    where
        T1: Into<WasmConst>,
        T2: Into<runwell::Type>,
    {
        let const_value = const_value.into().into_inner();
        let ty = ty.into();
        assert_eq!(const_value.ty(), ty);
        let result = self.builder.ins()?.constant(const_value)?;
        self.stack.push(result, ty);
        Ok(())
    }

    /// Extracts the float type from the generic Runwell type.
    ///
    /// # Note
    ///
    /// Use this only when certain due to Wasm validation that the given
    /// type must be an integer type.
    ///
    /// # Panics
    ///
    /// If the generic type does not contain an float type.
    fn extract_float_type(ty: runwell::Type) -> runwell::FloatType {
        match ty {
            runwell::Type::Float(float_type) => float_type,
            runwell::Type::Int(int_type) => {
                panic!("expected float type due to Wasm validation but found {} type.", int_type)
            }
            runwell::Type::Bool => {
                panic!("expected float type due to Wasm validation but found bool type.")
            }
        }
    }

    /// Translate a Wasm unary float operator into Runwell IR.
    fn translate_float_unop(
        &mut self,
        float_type: FloatType,
        op: UnaryFloatOp,
    ) -> Result<(), Error> {
        let source = self.stack.pop1()?;
        let actual_float_type = Self::extract_float_type(source.ty);
        assert_eq!(actual_float_type, float_type);
        let source = source.value;
        let ins = self.builder.ins()?;
        let result = match op {
            UnaryFloatOp::Abs => ins.fabs(float_type, source)?,
            UnaryFloatOp::Neg => ins.fneg(float_type, source)?,
            UnaryFloatOp::Sqrt => ins.fsqrt(float_type, source)?,
            UnaryFloatOp::Ceil => ins.fceil(float_type, source)?,
            UnaryFloatOp::Floor => ins.ffloor(float_type, source)?,
            UnaryFloatOp::Truncate => ins.ftruncate(float_type, source)?,
            UnaryFloatOp::Nearest => ins.fnearest(float_type, source)?,
        };
        self.stack.push(result, float_type.into());
        Ok(())
    }

    /// Translate a Wasm binary float operator into Runwell IR.
    fn translate_float_binop(
        &mut self,
        float_type: FloatType,
        op: BinaryFloatOp,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.stack.pop2()?;
        assert_eq!(lhs.ty, rhs.ty);
        let actual_float_type = Self::extract_float_type(lhs.ty);
        assert_eq!(actual_float_type, float_type);
        let ins = self.builder.ins()?;
        let lhs = lhs.value;
        let rhs = rhs.value;
        let result = match op {
            BinaryFloatOp::Add => ins.fadd(float_type, lhs, rhs)?,
            BinaryFloatOp::Sub => ins.fsub(float_type, lhs, rhs)?,
            BinaryFloatOp::Mul => ins.fmul(float_type, lhs, rhs)?,
            BinaryFloatOp::Div => ins.fdiv(float_type, lhs, rhs)?,
            BinaryFloatOp::Min => ins.fmin(float_type, lhs, rhs)?,
            BinaryFloatOp::Max => ins.fmax(float_type, lhs, rhs)?,
            BinaryFloatOp::CopySign => ins.fcopysign(float_type, lhs, rhs)?,
        };
        self.stack.push(result, float_type.into());
        Ok(())
    }

    /// Extracts the integer type from the generic Runwell type.
    ///
    /// # Note
    ///
    /// Use this only when certain due to Wasm validation that the given
    /// type must be an integer type.
    ///
    /// # Panics
    ///
    /// If the generic type does not contain an integer type.
    fn extract_int_type(ty: runwell::Type) -> runwell::IntType {
        match ty {
            runwell::Type::Int(int_type) => int_type,
            runwell::Type::Bool => {
                panic!("expected int type due to Wasm validation but found bool type.")
            }
            runwell::Type::Float(float_type) => {
                panic!("expected int type due to Wasm validation but found {} type.", float_type)
            }
        }
    }

    /// Translate a Wasm integer shift or rotate operator into Runwell IR.
    fn translate_int_shift(
        &mut self,
        int_type: IntType,
        op: ShiftIntOp,
    ) -> Result<(), Error> {
        let (source, shift_amount) = self.stack.pop2()?;
        assert_eq!(shift_amount.ty, IntType::I32.into());
        assert_eq!(source.ty, int_type.into());
        let ins = self.builder.ins()?;
        let source = source.value;
        let shift_amount = shift_amount.value;
        let result = match op {
            ShiftIntOp::Shl => ins.ishl(int_type, source, shift_amount)?,
            ShiftIntOp::Sshr => ins.isshr(int_type, source, shift_amount)?,
            ShiftIntOp::Ushr => ins.iushr(int_type, source, shift_amount)?,
            ShiftIntOp::Rotl => ins.irotl(int_type, source, shift_amount)?,
            ShiftIntOp::Rotr => ins.irotr(int_type, source, shift_amount)?,
        };
        self.stack.push(result, int_type.into());
        Ok(())
    }

    /// Translate a Wasm unary integer operator into Runwell IR.
    fn translate_int_unop(
        &mut self,
        int_type: IntType,
        op: UnaryIntOp,
    ) -> Result<(), Error> {
        let source = self.stack.pop1()?;
        let actual_int_ty = Self::extract_int_type(source.ty);
        assert_eq!(actual_int_ty, int_type);
        let ins = self.builder.ins()?;
        let source = source.value;
        let result = match op {
            UnaryIntOp::LeadingZeros => ins.iclz(int_type, source)?,
            UnaryIntOp::TrailingZeros => ins.ictz(int_type, source)?,
            UnaryIntOp::PopCount => ins.ipopcnt(int_type, source)?,
        };
        self.stack.push(result, int_type.into());
        Ok(())
    }

    /// Translate a Wasm binary integer operator into Runwell IR.
    fn translate_int_binop(
        &mut self,
        int_ty: IntType,
        op: BinaryIntOp,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.stack.pop2()?;
        assert_eq!(lhs.ty, rhs.ty);
        let actual_int_ty = Self::extract_int_type(lhs.ty);
        assert_eq!(actual_int_ty, int_ty);
        let ins = self.builder.ins()?;
        let lhs = lhs.value;
        let rhs = rhs.value;
        let result = match op {
            BinaryIntOp::Add => ins.iadd(int_ty, lhs, rhs)?,
            BinaryIntOp::Sub => ins.isub(int_ty, lhs, rhs)?,
            BinaryIntOp::Mul => ins.imul(int_ty, lhs, rhs)?,
            BinaryIntOp::Sdiv => ins.sdiv(int_ty, lhs, rhs)?,
            BinaryIntOp::Udiv => ins.udiv(int_ty, lhs, rhs)?,
            BinaryIntOp::Srem => ins.srem(int_ty, lhs, rhs)?,
            BinaryIntOp::Urem => ins.urem(int_ty, lhs, rhs)?,
            BinaryIntOp::And => ins.iand(int_ty, lhs, rhs)?,
            BinaryIntOp::Or => ins.ior(int_ty, lhs, rhs)?,
            BinaryIntOp::Xor => ins.ixor(int_ty, lhs, rhs)?,
        };
        self.stack.push(result, int_ty.into());
        Ok(())
    }

    /// Translates a Wasm integer compare to zero (Eqz) operator.
    fn translate_eqz_op(&mut self, int_type: IntType) -> Result<(), Error> {
        let source = self.stack.pop1()?;
        assert_eq!(source.ty.bit_width(), 32);
        let actual_int_type = Self::extract_int_type(source.ty);
        assert_eq!(actual_int_type, int_type);
        let zero_const: runwell::Const = match int_type {
            IntType::I32 => IntConst::I32(0).into(),
            IntType::I64 => IntConst::I64(0).into(),
            unsupported => {
                panic!(
                "encountered unsupported integer type {} for Wasm Eqz operator",
                unsupported
            )
            }
        };
        let zero = self.builder.ins()?.constant(zero_const)?;
        let result = self.builder.ins()?.icmp(
            int_type,
            CompareIntOp::Eq,
            source.value,
            zero,
        )?;
        self.stack.push(result, runwell::Type::Bool);
        Ok(())
    }

    /// Translates a Wasm integer compare operator.
    fn translate_icmp_op(
        &mut self,
        op: CompareIntOp,
        int_type: IntType,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.stack.pop2()?;
        assert_eq!(lhs.ty, rhs.ty);
        let actual_int_type = Self::extract_int_type(lhs.ty);
        assert_eq!(actual_int_type, int_type);
        let result = self
            .builder
            .ins()?
            .icmp(int_type, op, lhs.value, rhs.value)?;
        self.stack.push(result, runwell::Type::Bool);
        Ok(())
    }

    /// Translates a Wasm floating point number compare operator.
    fn translate_fcmp_op(
        &mut self,
        op: CompareFloatOp,
        float_ty: FloatType,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.stack.pop2()?;
        assert_eq!(lhs.ty, rhs.ty);
        assert_eq!(lhs.ty, float_ty.into());
        let int_type = Self::extract_int_type(lhs.ty);
        let result = self
            .builder
            .ins()?
            .fcmp(float_ty, op, lhs.value, rhs.value)?;
        self.stack.push(result, runwell::Type::Bool);
        Ok(())
    }

    /// Translates a Wasm `Select` or `TypedSelect` operator.
    fn translate_select_op(
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
