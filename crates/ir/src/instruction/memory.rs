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

use crate::primitive::{Const, Mem, Type, Value};
use derive_more::Display;

/// Represents the alignment of a store or load instruction.
///
/// The alignment is stored as `N` in `2^N`.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Alignment {
    value: u8,
}

impl Alignment {
    /// Creates a new alignment from the given value.
    pub fn new(value: u8) -> Self {
        Self { value }
    }

    /// Returns the alignment in bytes.
    pub fn get_in_bytes(&self) -> u32 {
        1u32.wrapping_shl(self.value as u32)
    }
}

/// Loads a value of type `ty` from the given memory at the given address with given alignment.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "load {} from {}+{}", ty, address, offset)]
pub struct LoadInstr {
    ty: Type,
    address: Value,
    offset: Const,
}

impl LoadInstr {
    /// Creates a new load instruction.
    ///
    /// Loads a value of type `ty` from the given memory at the given address.
    pub fn new(ty: Type, address: Value, offset: Const) -> Self {
        Self {
            ty,
            address,
            offset,
        }
    }

    /// Returns the address where to store the value in linear memory.
    pub fn address(&self) -> Value {
        self.address
    }

    /// Returns the address offset of the store instruction.
    pub fn offset(&self) -> Const {
        self.offset
    }

    /// Returns the type of the value that is stored in linear memory.
    pub fn ty(&self) -> Type {
        self.ty
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.address)
    }
}

/// Stores the value at the given address and offset.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "store {} {} from {}+{}", ty, value, address, offset)]
pub struct StoreInstr {
    address: Value,
    offset: Const,
    value: Value,
    ty: Type,
}

impl StoreInstr {
    /// Creates a new store instruction.
    ///
    /// Stores the value to the given memory at the given address with alignment.
    pub fn new(address: Value, offset: Const, value: Value, ty: Type) -> Self {
        Self {
            address,
            offset,
            value,
            ty,
        }
    }

    /// Returns the address where to store the value in linear memory.
    pub fn address(&self) -> Value {
        self.address
    }

    /// Returns the address offset of the store instruction.
    pub fn offset(&self) -> Const {
        self.offset
    }

    /// Returns the value that is to be stored in linear memory.
    pub fn value(&self) -> Value {
        self.value
    }

    /// Returns the type of the value that is stored in linear memory.
    pub fn ty(&self) -> Type {
        self.ty
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.address) || replace(&mut self.value)
    }
}

/// Grows the indexed linear memory by the given amount of new memory pages.
///
/// Returns the previous size of the linear memory upon success or -1 upon failure.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "memory.grow memory {}, pages {}", memory, new_pages)]
pub struct MemoryGrowInstr {
    memory: Mem,
    new_pages: Value,
}

impl MemoryGrowInstr {
    /// Creates a new memory grow instruction to grow the indexed linear memory.
    pub fn new(memory: Mem, new_pages: Value) -> Self {
        Self { memory, new_pages }
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.new_pages)
    }
}

/// Returns the current number of pages of the indexed linear memory.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "memory.size memory {}", memory)]
pub struct MemorySizeInstr {
    memory: Mem,
}

impl MemorySizeInstr {
    /// Creates a new memory size instruction to return the size (in pages) of the indexed linear memory.
    pub fn new(memory: Mem) -> Self {
        Self { memory }
    }
}
