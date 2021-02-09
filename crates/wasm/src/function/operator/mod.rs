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

mod base;
mod call;
mod control;
mod float;
mod int;
mod local_global;
mod memory;
mod util;

use super::FunctionBodyTranslator;
use crate::{Error, TranslateError, Type};
use core::convert::TryFrom as _;
use ir::instr::operands::{
    BinaryFloatOp,
    BinaryIntOp,
    CompareFloatOp,
    CompareIntOp,
    ShiftIntOp,
    UnaryFloatOp,
    UnaryIntOp,
};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translate a single Wasm operand into Runwell IR.
    #[rustfmt::skip]
    pub(super) fn translate_operator(
        &mut self,
        offset: usize,
        op: wasmparser::Operator,
    ) -> Result<(), Error> {
        use wasmparser::Operator as Op;
        use BinaryFloatOp as BinFloatOp;
        use CompareFloatOp as CmpFloatOp;
        use CompareIntOp as CmpIntOp;
        use ir::primitive::FloatType::{F32, F64};
        use ir::primitive::IntType::{I16, I32, I64, I8};
        use UnaryFloatOp as FloatUnop;
        use UnaryIntOp::*;
        // println!("op = {:?}", op);
        match op {
            Op::Unreachable => {
                self.builder.ins()?.trap()?;
            }
            Op::Nop => { /* Deliberately do nothing. */ }
            Op::Block { ty } => self.translate_block(ty)?,
            Op::Loop { ty } => self.translate_loop(ty)?,
            Op::If { ty } => self.translate_if(ty)?,
            Op::Else => self.translate_else()?,
            Op::End => self.translate_end()?,
            Op::Br { relative_depth } => self.translate_br(relative_depth)?,
            Op::BrIf { relative_depth } => self.translate_br_if(relative_depth)?,
            Op::BrTable { table } => self.translate_br_table(table)?,
            Op::Return => self.translate_return()?,
            Op::Call { function_index } => self.translate_call(function_index)?,
            Op::CallIndirect { index, table_index } => {
                self.translate_call_indirect(index, table_index)?
            }
            Op::ReturnCall { function_index } => self.translate_return_call(function_index)?,
            Op::ReturnCallIndirect { index, table_index } => {
                self.translate_return_call_indirect(index, table_index)?
            }
            Op::Drop => {
                self.stack.pop1()?;
            }
            Op::Select => self.translate_select_op(None)?,
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
            Op::GlobalGet { global_index } => self.translate_global_get(global_index)?,
            Op::GlobalSet { global_index } => self.translate_global_set(global_index)?,
            Op::I32Load { memarg } => self.translate_load(memarg, I32)?,
            Op::I64Load { memarg } => self.translate_load(memarg, I64)?,
            Op::F32Load { memarg } => self.translate_load(memarg, F32)?,
            Op::F64Load { memarg } => self.translate_load(memarg, F64)?,
            Op::I32Load8S { memarg } => self.translate_load_extend(memarg, I8, I32, true)?,
            Op::I32Load8U { memarg } => self.translate_load_extend(memarg, I8, I32, false)?,
            Op::I32Load16S { memarg } => self.translate_load_extend(memarg, I16, I32, true)?,
            Op::I32Load16U { memarg } => self.translate_load_extend(memarg, I16, I32, false)?,
            Op::I64Load8S { memarg } => self.translate_load_extend(memarg, I8, I64, true)?,
            Op::I64Load8U { memarg } => self.translate_load_extend(memarg, I8, I64, false)?,
            Op::I64Load16S { memarg } => self.translate_load_extend(memarg, I16, I64, true)?,
            Op::I64Load16U { memarg } => self.translate_load_extend(memarg, I16, I64, false)?,
            Op::I64Load32S { memarg } => self.translate_load_extend(memarg, I32, I64, true)?,
            Op::I64Load32U { memarg } => self.translate_load_extend(memarg, I32, I64, false)?,
            Op::I32Store { memarg } => self.translate_store(memarg, I32)?,
            Op::I64Store { memarg } => self.translate_store(memarg, I64)?,
            Op::F32Store { memarg } => self.translate_store(memarg, F32)?,
            Op::F64Store { memarg } => self.translate_store(memarg, F64)?,
            Op::I32Store8 { memarg } => self.translate_truncate_store(memarg, I32, I8)?,
            Op::I32Store16 { memarg } => self.translate_truncate_store(memarg, I32, I16)?,
            Op::I64Store8 { memarg } => self.translate_truncate_store(memarg, I64, I8)?,
            Op::I64Store16 { memarg } => self.translate_truncate_store(memarg, I64, I16)?,
            Op::I64Store32 { memarg } => self.translate_truncate_store(memarg, I64, I32)?,
            Op::MemorySize { mem, mem_byte } => self.translate_memory_size(mem, mem_byte)?,
            Op::MemoryGrow { mem, mem_byte } => self.translate_memory_grow(mem, mem_byte)?,
            Op::I32Const { value } => self.translate_const_op(value, I32)?,
            Op::I64Const { value } => self.translate_const_op(value, I64)?,
            Op::F32Const { value } => self.translate_const_op(value, F32)?,
            Op::F64Const { value } => self.translate_const_op(value, F64)?,
            Op::I32Eqz => self.translate_eqz_op(I32)?,
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
            Op::I64Eqz => self.translate_eqz_op(I64)?,
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
            Op::I32ReinterpretF32 => self.translate_reinterpret(F32, I32)?,
            Op::I64ReinterpretF64 => self.translate_reinterpret(F64, I64)?,
            Op::F32ReinterpretI32 => self.translate_reinterpret(I32, F32)?,
            Op::F64ReinterpretI64 => self.translate_reinterpret(I64, F64)?,
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
}
