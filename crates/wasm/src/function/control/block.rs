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

use crate::Error;
use core::convert::TryFrom;
use entity::RawIdx;
use ir::primitive::{FuncType, Type};
use module::ModuleResources;

/// The type of a Wasm block.
#[derive(Debug, Copy, Clone)]
pub enum WasmBlockType {
    /// Block has no inputs and no outputs.
    Empty,
    /// Block just returns the inner type and has no inputs.
    Returns(Type),
    /// Block is equal to the function type found in the module under the given index.
    FuncType(FuncType),
}

impl From<FuncType> for WasmBlockType {
    fn from(func_type: FuncType) -> Self {
        Self::FuncType(func_type)
    }
}

impl TryFrom<wasmparser::TypeOrFuncType> for WasmBlockType {
    type Error = Error;

    fn try_from(
        block_type: wasmparser::TypeOrFuncType,
    ) -> Result<Self, Self::Error> {
        let block_type = match block_type {
            wasmparser::TypeOrFuncType::Type(
                wasmparser::Type::EmptyBlockType,
            ) => Self::Empty,
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
