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

use super::super::{blocks::WasmBlock, FunctionBodyTranslator};
use crate::{Error, TranslateError};

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    /// Translate a Wasm `Block` control operator.
    pub(super) fn translate_block(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let wasm_block = WasmBlock::new(None, ty)?;
        self.blocks.push_block(wasm_block);
        Ok(())
    }

    /// Translate a Wasm `Loop` control operator.
    pub(super) fn translate_loop(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        let loop_header = self.builder.create_block()?;
        let wasm_block = WasmBlock::new(loop_header, ty)?;
        self.blocks.push_block(wasm_block);
        self.builder.ins()?.br(loop_header, vec![])?;
        self.builder.switch_to_block(loop_header)?;
        Ok(())
    }

    /// Translate a Wasm `If` control operator.
    pub(super) fn translate_if(
        &mut self,
        ty: wasmparser::TypeOrFuncType,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::If { ty },
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `Else` control operator.
    pub(super) fn translate_else(&mut self) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::Else,
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `End` control operator.
    pub(super) fn translate_end(&mut self) -> Result<(), Error> {
        let block = self.blocks.pop_block()?;
        if let Some(runwell_block) = block.block() {
            let _ = self.builder.seal_block(runwell_block).unwrap_or(());
        }
        if self.blocks.is_empty() {
            // The popped block was the entry block and thus the
            // `End` operator represents the end of the Wasm function.
            // Therefore we need to insert a Runwell return statement
            // returning all values that are still on the stack and
            // check if they are matching the functions return types.
            let outputs = self
                .res
                .get_func_type(self.func)
                .unwrap_or_else(|| {
                    panic!(
                        "expected function type for {} due to validation",
                        self.func
                    )
                })
                .outputs();
            let output_values = self.value_stack.peek_n(outputs.len())?;
            for (req_type, entry) in
                outputs.iter().copied().zip(output_values.clone())
            {
                assert_eq!(req_type, entry.ty);
            }
            self.builder
                .ins()?
                .return_values(output_values.map(|entry| entry.value))?;
            self.value_stack.pop_n(outputs.len())?;
        }
        Ok(())
    }

    /// Translate a Wasm `Br` control operator.
    pub(super) fn translate_br(
        &mut self,
        relative_depth: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::Br { relative_depth },
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `BrIf` control operator.
    pub(super) fn translate_br_if(
        &mut self,
        relative_depth: u32,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::BrIf { relative_depth },
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `BrTable` control operator.
    pub(super) fn translate_br_table(
        &mut self,
        table: wasmparser::BrTable,
    ) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::BrTable { table },
        ))
        .map_err(Into::into)
    }

    /// Translate a Wasm `Return` control operator.
    pub(super) fn translate_return(&mut self) -> Result<(), Error> {
        Err(TranslateError::unimplemented_operator(
            wasmparser::Operator::Return,
        ))
        .map_err(Into::into)
    }
}
