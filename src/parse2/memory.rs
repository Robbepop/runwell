// Copyright 2020 Robin Freyler
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

use crate::Index32;
use super::{InitializerExpr, LinearMemoryId, ParseError};
use core::convert::TryFrom;
use derive_more::Display;

/// An error that can occure upon parsing and validating linear memory.
#[derive(Debug, Display)]
pub enum MemoryError {
    #[display(fmt = "encountered unsupported 64-bit linear memory: {:?}", _0)]
    Unsupported64BitMemory(wasmparser::MemoryType),
    #[display(fmt = "encountered unsupported passive data kind")]
    UnsupportedPassiveData,
}

impl std::error::Error for MemoryError {}

/// A Wasm linear memory declaration.
#[derive(Debug, PartialEq, Eq)]
pub struct LinearMemory {
    initial_size: u32,
    maximum_size: Option<u32>,
    shared: bool,
}

impl LinearMemory {
    /// Returns the initial size of the linear memory.
    pub fn initial_size(&self) -> u32 {
        self.initial_size
    }

    /// Returns the maximum size of the linear memory if any.
    pub fn maximum_size(&self) -> Option<u32> {
        self.maximum_size
    }

    /// Returns `true` if the linear memory is shared.
    pub fn shared(&self) -> bool {
        self.shared
    }
}

impl TryFrom<wasmparser::MemoryType> for LinearMemory {
    type Error = ParseError;

    fn try_from(
        memory_type: wasmparser::MemoryType,
    ) -> Result<Self, Self::Error> {
        match memory_type {
            wasmparser::MemoryType::M32 { limits, shared } => {
                let initial_size = limits.initial;
                let maximum_size = limits.maximum;
                Ok(Self {
                    initial_size,
                    maximum_size,
                    shared,
                })
            }
            wasmparser::MemoryType::M64 { .. } => {
                Err(MemoryError::Unsupported64BitMemory(memory_type))
                    .map_err(Into::into)
            }
        }
    }
}

/// A data section item coming from the Wasm parser.
#[derive(Debug, Clone)]
pub struct Data<'a> {
    id: LinearMemoryId,
    offset: InitializerExpr,
    init: &'a [u8],
}

impl<'a> Data<'a> {
    /// Returns the linear memory ID of the data segment.
    pub fn memory_id(&self) -> LinearMemoryId {
        self.id
    }

    /// Returns the expression denoting the offset for the data segment.
    pub fn offset(&self) -> &InitializerExpr {
        &self.offset
    }

    /// Returns the bytes to initialize the linear memory.
    pub fn init(&self) -> &'a [u8] {
        &self.init
    }
}

impl<'a> TryFrom<wasmparser::Data<'a>> for Data<'a> {
    type Error = ParseError;

    fn try_from(value: wasmparser::Data<'a>) -> Result<Self, Self::Error> {
        match value.kind {
            wasmparser::DataKind::Active {
                memory_index,
                init_expr,
            } => {
                let id = LinearMemoryId::from_u32(memory_index);
                let offset = InitializerExpr::try_from(init_expr)?;
                Ok(Self {
                    id,
                    offset,
                    init: value.data,
                })
            }
            wasmparser::DataKind::Passive => {
                Err(MemoryError::UnsupportedPassiveData).map_err(Into::into)
            }
        }
    }
}
