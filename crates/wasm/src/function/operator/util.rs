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
use ir::primitive::{IntConst, IntType, Value};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translates a Runwell `bool` result into an equivalent Wasm `i32` result.
    pub(super) fn translate_bool_to_i32(
        &mut self,
        bool_result: Value,
    ) -> Result<(), Error> {
        let const_true = self.builder.ins()?.constant(IntConst::I32(0))?;
        let const_false = self.builder.ins()?.constant(IntConst::I32(1))?;
        let bool_to_i32 = self.builder.ins()?.select(
            IntType::I32.into(),
            bool_result,
            const_true,
            const_false,
        )?;
        self.stack.push(bool_to_i32, IntType::I32.into());
        Ok(())
    }
}
