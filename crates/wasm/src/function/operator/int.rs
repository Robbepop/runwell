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

use super::super::FunctionBodyTranslator;
use crate::Error;
use ir::{
    instr::operands::{BinaryIntOp, CompareIntOp, ShiftIntOp, UnaryIntOp},
    primitive as runwell,
    primitive::{FloatType, IntConst, IntType},
};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
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
            unmatched => {
                panic!("expected integer type due to Wasm validation but found {} type.", ty)
            }
        }
    }

    /// Translate a Wasm integer shift or rotate operator into Runwell IR.
    pub(super) fn translate_int_shift(
        &mut self,
        int_type: IntType,
        op: ShiftIntOp,
    ) -> Result<(), Error> {
        let (source, shift_amount) = self.value_stack.pop2()?;
        assert_eq!(self.builder.value_type(source), int_type.into());
        // Wasm expects both operands for shift operations to be of the same
        // type while Runwell always expects the shift amount to be of type
        // `i32`. Because of this we need to truncate in case the shift amount
        // is of type `i64`.
        let shift_amount = if int_type == IntType::I64 {
            self.builder.ins()?.itruncate(
                IntType::I64,
                IntType::I32,
                shift_amount,
            )?
        } else {
            shift_amount
        };
        let source = source;
        let ins = self.builder.ins()?;
        let result = match op {
            ShiftIntOp::Shl => ins.ishl(int_type, source, shift_amount)?,
            ShiftIntOp::Sshr => ins.isshr(int_type, source, shift_amount)?,
            ShiftIntOp::Ushr => ins.iushr(int_type, source, shift_amount)?,
            ShiftIntOp::Rotl => ins.irotl(int_type, source, shift_amount)?,
            ShiftIntOp::Rotr => ins.irotr(int_type, source, shift_amount)?,
        };
        self.value_stack.push(result);
        Ok(())
    }

    /// Translate a Wasm unary integer operator into Runwell IR.
    pub(super) fn translate_int_unop(
        &mut self,
        int_type: IntType,
        op: UnaryIntOp,
    ) -> Result<(), Error> {
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        let actual_int_ty = Self::extract_int_type(source_type);
        assert_eq!(actual_int_ty, int_type);
        let ins = self.builder.ins()?;
        let result = match op {
            UnaryIntOp::LeadingZeros => ins.iclz(int_type, source)?,
            UnaryIntOp::TrailingZeros => ins.ictz(int_type, source)?,
            UnaryIntOp::PopCount => ins.ipopcnt(int_type, source)?,
        };
        self.value_stack.push(result);
        Ok(())
    }

    /// Translate a Wasm binary integer operator into Runwell IR.
    pub(super) fn translate_int_binop(
        &mut self,
        int_ty: IntType,
        op: BinaryIntOp,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.value_stack.pop2()?;
        let lhs_type = self.builder.value_type(lhs);
        let rhs_type = self.builder.value_type(rhs);
        assert_eq!(lhs_type, rhs_type);
        let actual_int_ty = Self::extract_int_type(lhs_type);
        assert_eq!(actual_int_ty, int_ty);
        let ins = self.builder.ins()?;
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
        self.value_stack.push(result);
        Ok(())
    }

    /// Translates a Wasm integer compare to zero (`Eqz`) operator.
    pub(super) fn translate_eqz_op(
        &mut self,
        int_type: IntType,
    ) -> Result<(), Error> {
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        let actual_int_type = Self::extract_int_type(source_type);
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
            source,
            zero,
        )?;
        self.translate_bool_to_i32(result)?;
        Ok(())
    }

    /// Translates a Wasm integer compare operator.
    pub(super) fn translate_icmp_op(
        &mut self,
        op: CompareIntOp,
        int_type: IntType,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.value_stack.pop2()?;
        let lhs_type = self.builder.value_type(lhs);
        let rhs_type = self.builder.value_type(rhs);
        assert_eq!(lhs_type, rhs_type);
        let actual_int_type = Self::extract_int_type(lhs_type);
        assert_eq!(actual_int_type, int_type);
        let result = self.builder.ins()?.icmp(int_type, op, lhs, rhs)?;
        self.translate_bool_to_i32(result)?;
        Ok(())
    }

    /// Translates a Wasm integer extend operator.
    pub(super) fn translate_extend<SrcType, DstType>(
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
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        assert_eq!(source_type, src_type.into());
        let source = source;
        let result = self
            .builder
            .ins()?
            .iextend(src_type, dst_type, source, src_signed)?;
        self.value_stack.push(result);
        Ok(())
    }

    /// Translates a Wasm integer truncate operator.
    pub(super) fn translate_truncate<SrcType, DstType>(
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
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        assert_eq!(source_type, src_type.into());
        let source = source;
        let result =
            self.builder.ins()?.itruncate(src_type, dst_type, source)?;
        self.value_stack.push(result);
        Ok(())
    }

    /// Translates a Wasm integer to float conversion.
    pub(super) fn translate_int_to_float<SrcType, DstType>(
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
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        assert_eq!(source_type, src_type.into());
        let source = source;
        let result = self
            .builder
            .ins()?
            .int_to_float(src_signed, src_type, dst_type, source)?;
        self.value_stack.push(result);
        Ok(())
    }
}
