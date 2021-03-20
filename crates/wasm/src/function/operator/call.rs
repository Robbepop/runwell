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
use crate::{Error, TranslateError};
use entity::RawIdx;
use ir::primitive::Func;

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translates a Wasm function call.
    pub(super) fn translate_call(
        &mut self,
        function_index: u32,
    ) -> Result<(), Error> {
        let func = Func::from_raw(RawIdx::from_u32(function_index));
        let func_type = self.res.get_func_type(func).unwrap_or_else(|| {
            panic!("function type for {} must exist due to validation", func)
        });
        let len_inputs = func_type.inputs().len();
        let params = self.value_stack.pop_n(len_inputs).unwrap_or_else(|_| {
            panic!(
                "expect {} arguments on the stack due to validation",
                len_inputs
            )
        });
        let instr = self.builder.ins()?.call(func, params)?;
        self.value_stack
            .extend(self.builder.instr_values(instr)?.iter().copied());
        Ok(())
    }

    /// Translates a Wasm indirect function call.
    pub(super) fn translate_return_call(
        &mut self,
        function_index: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::ReturnCall { function_index },
        ))
        .map_err(Into::into)
    }

    /// Translates a Wasm indirect function call.
    pub(super) fn translate_call_indirect(
        &mut self,
        index: u32,
        table_index: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::CallIndirect { index, table_index },
        ))
        .map_err(Into::into)
    }

    /// Translates a Wasm indirect function call.
    pub(super) fn translate_return_call_indirect(
        &mut self,
        index: u32,
        table_index: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::ReturnCallIndirect { index, table_index },
        ))
        .map_err(Into::into)
    }
}
