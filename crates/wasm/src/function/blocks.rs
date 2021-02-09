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

#![allow(dead_code)]

use crate::{Error, TranslateError};
use core::convert::TryFrom;
use entity::RawIdx;
use ir::primitive::{Block, FuncType, Type};
use module::ModuleResources;

/// A stack of Wasm `Block` and `Loop` definitions to branch/continue to.
#[derive(Debug, Default)]
pub struct Blocks {
    blocks: Vec<WasmBlock>,
}

impl Blocks {
    /// Returns `true` if the stack of blocks is empty.
    ///
    /// # Note
    ///
    /// This is usually the case after translating the last `End` Wasm operator
    /// of a Wasm function.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the current depth of the stack of Wasm blocks.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Pushes the Wasm `Block` or `Loop` onto the stack of blocks.
    pub fn push_block(&mut self, block: WasmBlock) {
        self.blocks.push(block)
    }

    /// Pops the latest inserted Wasm block from the stack of blocks and returns it.
    ///
    /// # Errors
    ///
    /// If the stack of blocks is empty.
    pub fn pop_block(&mut self) -> Result<WasmBlock, TranslateError> {
        self.blocks.pop().ok_or(TranslateError::MissingWasmBlock)
    }

    /// Returns the n-th Wasm block from the back where 0-th is the last.
    ///
    /// # Errors
    ///
    /// If `n` exceeds the length of the stack of blocks.
    pub fn nth_back(&self, n: u32) -> Result<WasmBlock, TranslateError> {
        self.blocks
            .iter()
            .rev()
            .nth_back(n as usize)
            .copied()
            .ok_or_else(|| {
                let len = self.blocks.len();
                TranslateError::RelativeDepthExceedsBlockStack { n, len }
            })
    }

    /// Returns the current Wasm block.
    ///
    /// This is the Wasm block that was put latest on the stack of blocks.
    ///
    /// # Errors
    ///
    /// If the stack of blocks is empty.
    pub fn current(&self) -> Result<WasmBlock, TranslateError> {
        self.blocks
            .last()
            .copied()
            .ok_or(TranslateError::MissingWasmBlock)
    }
}

/// A Wasm `Block` or `Loop` for Wasm operators to branch to.
#[derive(Debug, Copy, Clone)]
pub struct WasmBlock {
    /// The unique Runwell basic block index of the Wasm block.
    block: Block,
    /// The type of the Wasm block.
    ty: WasmBlockType,
}

impl WasmBlock {
    /// Creates a new Wasm block with the given block type.
    pub fn new(
        block: Block,
        block_type: wasmparser::TypeOrFuncType,
    ) -> Result<Self, Error> {
        Ok(Self {
            block,
            ty: WasmBlockType::try_from(block_type)?,
        })
    }

    /// Creates a new Wasm block with the given function type.
    pub fn with_func_type(block: Block, func_type: FuncType) -> Self {
        Self {
            block,
            ty: WasmBlockType::FuncType(func_type),
        }
    }

    /// Returns the associated Runwell block index.
    pub fn block(&self) -> Block {
        self.block
    }

    /// Returns a slice over the input types of the Wasm block.
    pub fn inputs<'a, 'b, 'c>(&'a self, res: &'b ModuleResources) -> &'c [Type]
    where
        'a: 'c,
        'b: 'c,
    {
        self.ty.inputs(res)
    }

    /// Returns a slice over the output types of the Wasm block.
    pub fn outputs<'a, 'b, 'c>(&'a self, res: &'b ModuleResources) -> &'c [Type]
    where
        'a: 'c,
        'b: 'c,
    {
        self.ty.outputs(res)
    }
}

/// The type of a Wasm block.
#[derive(Debug, Copy, Clone)]
enum WasmBlockType {
    /// Block has no inputs and no outputs.
    Empty,
    /// Block just returns the inner type and has no inputs.
    Returns(Type),
    /// Block is equal to the function type found in the module under the given index.
    FuncType(FuncType),
}

impl TryFrom<wasmparser::TypeOrFuncType> for WasmBlockType {
    type Error = Error;

    fn try_from(
        block_type: wasmparser::TypeOrFuncType,
    ) -> Result<Self, Self::Error> {
        let block_type = match block_type {
            wasmparser::TypeOrFuncType::Type(wasmparser::Type::EmptyBlockType) => {
                Self::Empty
            }
            wasmparser::TypeOrFuncType::Type(ty) => {
                Self::Returns(crate::Type::try_from(ty)?.into_inner())
            }
            wasmparser::TypeOrFuncType::FuncType(func_type) => {
                let func_type = FuncType::from_raw(RawIdx::from_u32(func_type));
                Self::FuncType(func_type)
            }
        };
        Ok(block_type)
    }
}

impl WasmBlockType {
    /// Returns a slice over the input types of the Wasm block.
    pub fn inputs<'a, 'b, 'c>(&'a self, res: &'b ModuleResources) -> &'c [Type]
    where
        'a: 'c,
        'b: 'c,
    {
        match self {
            Self::Empty | Self::Returns(_) => &[],
            Self::FuncType(func_type) => {
                res.get_type(*func_type)
                    .unwrap_or_else(|| {
                        panic!("expect block type due to validation")
                    })
                    .inputs()
            }
        }
    }

    /// Returns a slice over the output types of the Wasm block.
    pub fn outputs<'a, 'b, 'c>(&'a self, res: &'b ModuleResources) -> &'c [Type]
    where
        'a: 'c,
        'b: 'c,
    {
        match self {
            Self::Empty => &[],
            Self::Returns(return_type) => core::slice::from_ref(return_type),
            Self::FuncType(func_type) => {
                res.get_type(*func_type)
                    .unwrap_or_else(|| {
                        panic!("expect block type due to validation")
                    })
                    .outputs()
            }
        }
    }
}
