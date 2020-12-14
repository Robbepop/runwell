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

use crate::parse::{CompilerError, GlobalInitExpr, LinearMemoryId};
use core::convert::TryFrom;
use derive_more::Display;
use wasmparser::ResizableLimits;

/// An error that can occure upon interacting with Wasm linear memory.
#[derive(Debug, Display, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemoryError {
    #[display(
        fmt = "encountered an unsupported 64-bit linear memory declaration"
    )]
    Unsupported64BitLinearMemory,
    #[display(fmt = "encountered a linear memory out of bounds access")]
    MemoryAccessOutOfBounds,
}

impl MemoryError {
    /// Returns `true` if the error states that some unsupported Wasm definition has been encountered.
    pub fn is_unsupported_error(&self) -> bool {
        match self {
            Self::Unsupported64BitLinearMemory => true,
            _ => false,
        }
    }
}

/// A data segment coming from the Wasm parser.
#[derive(Debug, Clone)]
pub struct Data<'a> {
    id: LinearMemoryId,
    offset: GlobalInitExpr,
    init: &'a [u8],
}

impl<'a> Data<'a> {
    /// Returns the linear memory ID of the data segment.
    pub fn id(&self) -> LinearMemoryId {
        self.id
    }

    /// Returns the expression denoting the offset for the data segment.
    pub fn offset(&self) -> &GlobalInitExpr {
        &self.offset
    }

    /// Returns the bytes to initialize the linear memory.
    pub fn init(&self) -> &'a [u8] {
        &self.init
    }
}

impl<'a> TryFrom<wasmparser::Data<'a>> for Data<'a> {
    type Error = CompilerError;

    fn try_from(value: wasmparser::Data<'a>) -> Result<Self, Self::Error> {
        match value.kind {
            wasmparser::DataKind::Active {
                memory_index,
                init_expr,
            } => {
                let id = LinearMemoryId::from_u32(memory_index);
                let offset = GlobalInitExpr::try_from(init_expr)?;
                Ok(Self {
                    id,
                    offset,
                    init: value.data,
                })
            }
            wasmparser::DataKind::Passive => {
                Err(CompilerError::UnsupportedPassiveElement)
            }
        }
    }
}

/// A linear memory declaration.
#[derive(Debug)]
pub struct LinearMemoryDecl {
    limits: ResizableLimits,
    shared: bool,
    contents: LinearMemoryContents,
}

impl LinearMemoryDecl {
    /// Returns the initial linear memory size in bytes.
    pub fn initial_size(&self) -> u32 {
        self.limits.initial
    }

    /// Returns the maximum linear memory size in bytes if any.
    pub fn maximum_size(&self) -> Option<u32> {
        self.limits.maximum
    }

    /// Returns a mutable reference to the linear memory contents.
    pub fn contents(&mut self) -> &mut LinearMemoryContents {
        &mut self.contents
    }
}

impl TryFrom<wasmparser::MemoryType> for LinearMemoryDecl {
    type Error = CompilerError;

    fn try_from(
        memory_type: wasmparser::MemoryType,
    ) -> Result<Self, Self::Error> {
        match memory_type {
            wasmparser::MemoryType::M32 { limits, shared } => {
                Ok(Self {
                    limits,
                    shared,
                    contents: LinearMemoryContents::default(),
                })
            }
            wasmparser::MemoryType::M64 { .. } => {
                Err(MemoryError::Unsupported64BitLinearMemory)
                    .map_err(Into::into)
            }
        }
    }
}

/// The contents of a Wasm linear memory.
#[derive(Debug, Default)]
pub struct LinearMemoryContents {
    /// Contents of the linear memory.
    ///
    /// Uninitializes contents are set to 0 by default.
    contents: Vec<u8>,
}

impl LinearMemoryContents {
    /// Initializes the region starting at `offset` with the given byte sequence.
    ///
    /// Consecutive calls to `init_region` might overwrite past initializations.
    pub fn init_region(
        &mut self,
        start: u32,
        bytes: &[u8],
    ) -> Result<(), CompilerError> {
        let start = start as usize;
        let end = start + bytes.len();
        if self.contents.len() < end {
            self.contents.resize(end, 0u8);
        }
        self.contents[start..end].copy_from_slice(bytes);
        Ok(())
    }

    /// Returns the requested amount of bytes at the given offset if any.
    ///
    /// Returns `None` if `offset + len` is out of bounds for the memory.
    pub fn get(&self, offset: u32, len: usize) -> Option<&[u8]> {
        let offset = offset as usize;
        let req_len = offset + len;
        if req_len >= self.contents.len() {
            return None
        }
        let bytes = &self.contents[offset..(offset + len)];
        Some(bytes)
    }

    /// Writes the bytes at the given `offset` into `buffer`.
    ///
    /// Reads an amount of bytes equal to the length of the `buffer` and returns
    /// an error if this is not possible.
    pub fn read(
        &self,
        offset: u32,
        buffer: &mut [u8],
    ) -> Result<(), CompilerError> {
        let offset = offset as usize;
        let len = buffer.len();
        let req_len = offset + len;
        if req_len >= self.contents.len() {
            return Err(MemoryError::MemoryAccessOutOfBounds).map_err(Into::into)
        }
        buffer[..].copy_from_slice(&self.contents[offset..(offset + len)]);
        Ok(())
    }
}
