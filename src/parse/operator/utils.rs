// Copyright 2019 Robin Freyler
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

use crate::parse::Identifier;

/// Memory access parameters.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoryImmediate {
    /// The offset of the memory access.
    offset: usize,
    /// The alignment of the memory access.
    ///
    /// Given as power of two:
    /// I.e. an `alignment` of `3` represents `2^3 = 8` bytes alignment.
    alignment: usize,
}

impl From<wasmparser::MemoryImmediate> for MemoryImmediate {
    fn from(imm: wasmparser::MemoryImmediate) -> Self {
        MemoryImmediate::new(imm.offset as usize, imm.align as usize)
    }
}

impl MemoryImmediate {
    /// Creates memory parameters for the given offset and alignment.
    ///
    /// # Note
    ///
    /// The alignment is given as power-of-two alignment.
    /// I.e. an `alignment` of `3` represents `2^3 = 8` bytes alignment.
    pub fn new(offset: usize, alignment: usize) -> Self {
        Self { offset, alignment }
    }

    /// Returns the offset.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the alignment as power-of-two.
    pub fn alignment(&self) -> usize {
        self.alignment
    }
}

/// A local variable ID.
///
/// Used to access local variables of Wasm functions.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalVariableId(pub(super) usize);

impl Identifier for LocalVariableId {
    fn get(self) -> usize {
        self.0
    }
}

/// Generates new unique local variable identifiers.
pub struct LocalVariableIdGen {
    /// The current local variable identifier.
    current: usize,
}

impl LocalVariableIdGen {
    /// Creates a new local variable generator.
    pub fn new() -> Self {
        Self { current: 0 }
    }

    /// Generates a new unique local variable identifier.
    pub fn gen(&mut self) -> LocalVariableId {
        let result = LocalVariableId(self.current);
        self.current += 1;
        result
    }
}

/// The extended set of integer types.
///
/// # Note
///
/// Required for generic `load` and `store` as well as for
/// conversion routines.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExtIntType {
    /// 8-bit integer type.
    I8,
    /// 16-bit integer type.
    I16,
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

impl ExtIntType {
    /// Returns `true` if `self` type is extendable to the `dst` type.
    pub fn is_extendable_to(self, dst: IntType) -> bool {
        self.width() < dst.width()
    }

    /// Returns the number of bytes used to represent a value of the type.
    pub fn width(self) -> usize {
        match self {
            ExtIntType::I8 => 1,
            ExtIntType::I16 => 2,
            ExtIntType::I32 => 4,
            ExtIntType::I64 => 8,
        }
    }
}

impl From<IntType> for ExtIntType {
    fn from(int_ty: IntType) -> Self {
        match int_ty {
            IntType::I32 => ExtIntType::I32,
            IntType::I64 => ExtIntType::I64,
        }
    }
}

/// A Wasm integer type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntType {
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

impl IntType {
    /// Returns `true` if `self` is truncatable to the `dst` type.
    pub fn is_truncatable_to(self, dst: ExtIntType) -> bool {
        self.width() > dst.width()
    }

    /// Returns the number of bytes used to represent a value of the type.
    pub fn width(self) -> usize {
        match self {
            IntType::I32 => 4,
            IntType::I64 => 8,
        }
    }
}
