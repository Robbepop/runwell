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
use entity::RawIdx;
use module::Variable;

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translates Wasm `local_get` operator.
    pub(in crate::function) fn translate_local_get(
        &mut self,
        local_index: u32,
    ) -> Result<(), Error> {
        let var = Variable::from_raw(RawIdx::from_u32(local_index));
        let result = self.builder.read_var(var)?;
        let result_type = self.builder.var_type(var)?;
        self.stack.push(result, result_type);
        Ok(())
    }

    /// Translates Wasm `local_set` operator.
    pub(in crate::function) fn translate_local_set(
        &mut self,
        local_index: u32,
    ) -> Result<(), Error> {
        let var = Variable::from_raw(RawIdx::from_u32(local_index));
        let source = self.stack.pop1()?;
        assert_eq!(self.builder.var_type(var)?, source.ty);
        self.builder.write_var(var, source.value)?;
        Ok(())
    }

    /// Translates Wasm `local_tee` operator.
    pub(in crate::function) fn translate_local_tee(
        &mut self,
        local_index: u32,
    ) -> Result<(), Error> {
        let var = Variable::from_raw(RawIdx::from_u32(local_index));
        let source = self.stack.peek1()?;
        assert_eq!(self.builder.var_type(var)?, source.ty);
        self.builder.write_var(var, source.value)?;
        Ok(())
    }
}
