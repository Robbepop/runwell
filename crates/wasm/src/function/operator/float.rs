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
    instr::operands::{BinaryFloatOp, CompareFloatOp, UnaryFloatOp},
    primitive as runwell,
    primitive::{FloatType, IntType},
};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
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
            unmatched => {
                panic!("expected float type due to Wasm validation but found {} type.", ty)
            }
        }
    }

    /// Translates a Wasm float to integer conversion.
    fn translate_float_to_int(
        &mut self,
        src_type: FloatType,
        dst_type: IntType,
        dst_signed: bool,
        saturating: bool,
    ) -> Result<(), Error> {
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        assert_eq!(source_type, src_type.into());
        let source = source;
        let result = self
            .builder
            .ins()?
            .float_to_int(src_type, dst_type, dst_signed, source, saturating)?;
        assert_eq!(self.builder.value_type(result), dst_type.into(),);
        self.value_stack.push(result);
        Ok(())
    }

    /// Translates a Wasm float to integer conversion.
    pub(super) fn translate_float_to_sint<SrcType, DstType>(
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
    pub(super) fn translate_float_to_sint_sat<SrcType, DstType>(
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
    pub(super) fn translate_float_to_uint<SrcType, DstType>(
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
    pub(super) fn translate_float_to_uint_sat<SrcType, DstType>(
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
    pub(super) fn translate_demote<FromType, ToType>(
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
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        assert_eq!(source_type, from_type.into());
        let result = self.builder.ins()?.demote(from_type, to_type, source)?;
        self.value_stack.push(result);
        Ok(())
    }

    /// Translates a Wasm promote operator.
    pub(super) fn translate_promote<FromType, ToType>(
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
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        assert_eq!(source_type, from_type.into());
        let result = self.builder.ins()?.promote(from_type, to_type, source)?;
        self.value_stack.push(result);
        Ok(())
    }

    /// Translates a Wasm floating point number compare operator.
    pub(super) fn translate_fcmp_op(
        &mut self,
        op: CompareFloatOp,
        float_type: FloatType,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.value_stack.pop2()?;
        let lhs_type = self.builder.value_type(lhs);
        let rhs_type = self.builder.value_type(rhs);
        assert_eq!(lhs_type, rhs_type);
        let actual_float_type = Self::extract_float_type(lhs_type);
        assert_eq!(actual_float_type, float_type);
        let result = self.builder.ins()?.fcmp(float_type, op, lhs, rhs)?;
        self.translate_bool_to_i32(result)?;
        Ok(())
    }

    /// Translate a Wasm unary float operator into Runwell IR.
    pub(super) fn translate_float_unop(
        &mut self,
        float_type: FloatType,
        op: UnaryFloatOp,
    ) -> Result<(), Error> {
        let source = self.value_stack.pop1()?;
        let source_type = self.builder.value_type(source);
        let actual_float_type = Self::extract_float_type(source_type);
        assert_eq!(actual_float_type, float_type);
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
        self.value_stack.push(result);
        Ok(())
    }

    /// Translate a Wasm binary float operator into Runwell IR.
    pub(super) fn translate_float_binop(
        &mut self,
        float_type: FloatType,
        op: BinaryFloatOp,
    ) -> Result<(), Error> {
        let (lhs, rhs) = self.value_stack.pop2()?;
        let lhs_type = self.builder.value_type(lhs);
        let rhs_type = self.builder.value_type(rhs);
        assert_eq!(lhs_type, rhs_type);
        let actual_float_type = Self::extract_float_type(lhs_type);
        assert_eq!(actual_float_type, float_type);
        let ins = self.builder.ins()?;
        let result = match op {
            BinaryFloatOp::Add => ins.fadd(float_type, lhs, rhs)?,
            BinaryFloatOp::Sub => ins.fsub(float_type, lhs, rhs)?,
            BinaryFloatOp::Mul => ins.fmul(float_type, lhs, rhs)?,
            BinaryFloatOp::Div => ins.fdiv(float_type, lhs, rhs)?,
            BinaryFloatOp::Min => ins.fmin(float_type, lhs, rhs)?,
            BinaryFloatOp::Max => ins.fmax(float_type, lhs, rhs)?,
            BinaryFloatOp::CopySign => ins.fcopysign(float_type, lhs, rhs)?,
        };
        self.value_stack.push(result);
        Ok(())
    }
}
