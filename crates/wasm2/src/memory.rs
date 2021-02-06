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

use super::{Error, InitExpr};
use core::convert::TryFrom;
use derive_more::Display;
use entity::RawIdx;
use ir::primitive::Mem;

/// An error that can occure upon parsing and validating linear memory.
#[derive(Debug, Display)]
pub enum MemoryError {
    #[display(fmt = "encountered unsupported 64-bit linear memory: {:?}", _0)]
    Unsupported64BitMemory(wasmparser::MemoryType),
    #[display(
        fmt = "encountered unsupported shared Wasm linear memory: {:?}",
        _0
    )]
    UnsupportedSharedMemory(wasmparser::MemoryType),
    #[display(fmt = "encountered unsupported passive data kind")]
    UnsupportedPassiveData,
}

impl std::error::Error for MemoryError {}

/// A Wasm linear memory declaration.
#[derive(Debug)]
pub struct LinearMemoryDecl {
    inner: module::LinearMemoryDecl,
}

impl LinearMemoryDecl {
    /// Returns the inner Runwell linear memory declaration.
    pub fn into_inner(self) -> module::LinearMemoryDecl {
        self.inner
    }
}

impl TryFrom<wasmparser::MemoryType> for LinearMemoryDecl {
    type Error = Error;

    fn try_from(
        memory_type: wasmparser::MemoryType,
    ) -> Result<Self, Self::Error> {
        match memory_type {
            wasmparser::MemoryType::M32 {
                limits,
                shared: false,
            } => {
                let initial_pages = limits.initial;
                let maximum_pages = limits.maximum;
                Ok(Self {
                    inner: module::LinearMemoryDecl::new(
                        initial_pages,
                        maximum_pages,
                    ),
                })
            }
            wasmparser::MemoryType::M32 { shared: true, .. } => {
                return Err(MemoryError::UnsupportedSharedMemory(memory_type))
                    .map_err(Into::into)
            }
            wasmparser::MemoryType::M64 { .. } => {
                Err(MemoryError::Unsupported64BitMemory(memory_type))
                    .map_err(Into::into)
            }
        }
    }
}

/// A data section item coming from the Wasm parser.
#[derive(Debug)]
pub struct MemoryDataInit<'a> {
    memory: Mem,
    offset: InitExpr,
    bytes: &'a [u8],
}

impl<'a> MemoryDataInit<'a> {
    /// Returns the linear memory ID of the data segment.
    pub fn memory(&self) -> Mem {
        self.memory
    }

    /// Returns the expression denoting the offset for the data segment.
    pub fn offset(self) -> InitExpr {
        self.offset
    }

    /// Returns the bytes to initialize the linear memory segment.
    pub fn bytes(&self) -> &'a [u8] {
        &self.bytes
    }
}

impl<'a> TryFrom<wasmparser::Data<'a>> for MemoryDataInit<'a> {
    type Error = Error;

    fn try_from(value: wasmparser::Data<'a>) -> Result<Self, Self::Error> {
        match value.kind {
            wasmparser::DataKind::Active {
                memory_index,
                init_expr,
            } => {
                let memory = Mem::from_raw(RawIdx::from_u32(memory_index));
                let offset = InitExpr::try_from(init_expr)?;
                Ok(Self {
                    memory,
                    offset,
                    bytes: value.data,
                })
            }
            wasmparser::DataKind::Passive => {
                Err(MemoryError::UnsupportedPassiveData).map_err(Into::into)
            }
        }
    }
}
