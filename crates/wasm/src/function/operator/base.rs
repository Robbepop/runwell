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
use crate::{Const, Error};
use ir::primitive::{self as runwell, IntType};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translates a Wasm reinterpret operator.
    pub(super) fn translate_reinterpret<FromType, ToType>(
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
        let source = self.value_stack.pop1()?;
        assert_eq!(source.ty, from_type);
        let result = self.builder.ins()?.reinterpret(
            from_type,
            to_type,
            source.value,
        )?;
        self.value_stack.push(result, to_type);
        Ok(())
    }

    /// Translates a Wasm constant operator.
    pub(super) fn translate_const_op<T1, T2>(
        &mut self,
        const_value: T1,
        ty: T2,
    ) -> Result<(), Error>
    where
        T1: Into<Const>,
        T2: Into<runwell::Type>,
    {
        let const_value = const_value.into().into_inner();
        let ty = ty.into();
        assert_eq!(const_value.ty(), ty);
        let result = self.builder.ins()?.constant(const_value)?;
        self.value_stack.push(result, ty);
        Ok(())
    }

    /// Translates a Wasm `Select` or `TypedSelect` operator.
    pub(super) fn translate_select_op(
        &mut self,
        required_ty: Option<runwell::Type>,
    ) -> Result<(), Error> {
        let (if_true, if_false, condition) = self.value_stack.pop3()?;
        assert_eq!(
            if_true.ty, if_false.ty,
            "due to validation both types must be equal"
        );
        if let Some(required_ty) = required_ty {
            assert_eq!(if_true.ty, required_ty);
        }
        let ty = if_true.ty;
        let condition_i1 = self.builder.ins()?.itruncate(
            IntType::I32,
            IntType::I1,
            condition.value,
        )?;
        let result = self.builder.ins()?.bool_select(
            ty,
            condition_i1,
            if_true.value,
            if_false.value,
        )?;
        self.value_stack.push(result, ty);
        Ok(())
    }
}
