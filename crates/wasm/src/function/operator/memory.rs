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
use crate::{function::stack::ValueEntry, Error, TranslateError};
use entity::RawIdx;
use ir::{
    primitive::{self as runwell, IntType, Mem, Value},
    ImmU32,
};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Builds a Wasm linear memory load operator.
    ///
    /// # Note
    ///
    /// Used by translators for Wasm load and store operators.
    fn build_heap_addr(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        pos: ValueEntry,
        ty: runwell::Type,
    ) -> Result<Value, Error> {
        assert_eq!(pos.ty, IntType::I32.into());
        let mem = Mem::from_raw(RawIdx::from_u32(memarg.memory));
        let pos = pos.value;
        let alignment_bytes = 2_u32.pow(ty.alignment() as u32);
        let size = ImmU32::from(alignment_bytes + memarg.offset);
        let ptr = self.builder.ins()?.heap_addr(mem, pos, size)?;
        Ok(ptr)
    }

    /// Translates a Wasm linear memory load operator.
    ///
    /// # Note
    ///
    /// Users should prefer using
    /// [`translate_load`][`FunctionBodyTranslator::translate_load`]
    /// over using this API directly.
    fn translate_load_typed(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        result_type: runwell::Type,
    ) -> Result<(), Error> {
        let pos = self.stack.pop1()?;
        let ptr = self.build_heap_addr(memarg, pos, result_type)?;
        let offset = ImmU32::from(memarg.offset);
        let result = self.builder.ins()?.load(ptr, offset, result_type)?;
        self.stack.push(result, result_type);
        Ok(())
    }

    /// Translates a Wasm linear memory load operator.
    pub(super) fn translate_load<T>(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        ty: T,
    ) -> Result<(), Error>
    where
        T: Into<runwell::Type>,
    {
        self.translate_load_typed(memarg, ty.into())
    }

    /// Translates a Wasm linear memory store operator.
    ///
    /// # Note
    ///
    /// Users should prefer using
    /// [`translate_store`][`FunctionBodyTranslator::translate_store`]
    /// over using this API directly.
    fn translate_store_typed(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        stored_type: runwell::Type,
    ) -> Result<(), Error> {
        let (pos, stored_value) = self.stack.pop2()?;
        assert_eq!(stored_value.ty, stored_type);
        let ptr = self.build_heap_addr(memarg, pos, stored_type)?;
        let offset = ImmU32::from(memarg.offset);
        let stored_value = stored_value.value;
        self.builder
            .ins()?
            .store(ptr, offset, stored_value, stored_type)?;
        Ok(())
    }

    /// Translates a Wasm linear memory load operator.
    pub(super) fn translate_store<T>(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        ty: T,
    ) -> Result<(), Error>
    where
        T: Into<runwell::Type>,
    {
        self.translate_store_typed(memarg, ty.into())
    }

    /// Translates a combined Wasm linear memory load and extend operator.
    pub(super) fn translate_load_extend(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        load_type: IntType,
        extend_type: IntType,
        extend_signed: bool,
    ) -> Result<(), Error> {
        self.translate_load(memarg, load_type)?;
        self.translate_extend(load_type, extend_type, extend_signed)?;
        Ok(())
    }

    /// Translates a combined Wasm linear memory truncate and store operator.
    pub(super) fn translate_truncate_store(
        &mut self,
        memarg: wasmparser::MemoryImmediate,
        truncated_type: IntType,
        stored_type: IntType,
    ) -> Result<(), Error> {
        self.translate_truncate(truncated_type, stored_type)?;
        self.translate_store(memarg, stored_type)?;
        Ok(())
    }

    /// Translates the Wasm memory grow operator.
    pub(super) fn translate_memory_grow(
        &mut self,
        mem: u32,
        mem_byte: u8,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::MemoryGrow { mem, mem_byte },
        ))
        .map_err(Into::into)
    }

    /// Translates the Wasm memory size operator.
    pub(super) fn translate_memory_size(
        &mut self,
        mem: u32,
        mem_byte: u8,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::MemorySize { mem, mem_byte },
        ))
        .map_err(Into::into)
    }
}
