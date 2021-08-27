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

use crate::{
    primitive::{Mem, Type, Value},
    VisitValues,
    VisitValuesMut,
};
use derive_more::{Display, From};

/// An immediate `u32` value of a Runwell IR instruction.
#[derive(
    Debug, Copy, Clone, Display, PartialEq, Eq, PartialOrd, Ord, Hash, From,
)]
pub struct ImmU64 {
    /// The underlying `u64` value.
    value: u64,
}

impl ImmU64 {
    /// Returns the inner raw `u64` value.
    pub fn into_inner(self) -> u64 {
        self.value
    }
}

/// Returns a pointer from the heap at the given location.
///
/// Checks if the range `ptr..ptr+size` is within bounds of the target heap memory.
/// The `load` and `store` instructions can use the address value returned by
/// this instruction in order to load or store values from and to the heap memory.
///
/// Traps if `ptr..ptr+size` is not within bounds for the target heap memory.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "heap_addr {}[{}..{}+{}]", heap, ptr, ptr, size)]
pub struct HeapAddrInstr {
    heap: Mem,
    ptr: Value,
    size: ImmU64,
}

impl HeapAddrInstr {
    /// Creates a new heap addressing instruction.
    pub fn new(heap: Mem, ptr: Value, size: ImmU64) -> Self {
        Self { heap, ptr, size }
    }

    /// Returns index of the heap to index into.
    pub fn heap(&self) -> Mem {
        self.heap
    }

    /// Returns the pointer where to index into the linear memory.
    pub fn ptr(&self) -> Value {
        self.ptr
    }

    /// Returns the size of the area to allow indexing into the linear memory.
    pub fn size(&self) -> ImmU64 {
        self.size
    }
}

impl VisitValues for HeapAddrInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.ptr);
    }
}

impl VisitValuesMut for HeapAddrInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.ptr);
    }
}

/// Loads a value of type `ty` from the given memory at the given address with given alignment.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "load {} from {}+{}", ty, address, offset)]
pub struct LoadInstr {
    ty: Type,
    address: Value,
    offset: ImmU64,
}

impl LoadInstr {
    /// Creates a new load instruction.
    pub fn new(ty: Type, address: Value, offset: ImmU64) -> Self {
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
    pub fn offset(&self) -> ImmU64 {
        self.offset
    }

    /// Returns the type of the value that is stored in linear memory.
    pub fn ty(&self) -> Type {
        self.ty
    }
}

impl VisitValues for LoadInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.address);
    }
}

impl VisitValuesMut for LoadInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.address);
    }
}

/// Stores the value at the given address and offset.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "store {} {} from {}+{}", ty, value, address, offset)]
pub struct StoreInstr {
    address: Value,
    offset: ImmU64,
    value: Value,
    ty: Type,
}

impl StoreInstr {
    /// Creates a new store instruction.
    pub fn new(address: Value, offset: ImmU64, value: Value, ty: Type) -> Self {
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
    pub fn offset(&self) -> ImmU64 {
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
}

impl VisitValues for StoreInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        let _ = visitor(self.address) && visitor(self.value);
    }
}

impl VisitValuesMut for StoreInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        let _ = visitor(&mut self.address) && visitor(&mut self.value);
    }
}

/// Grows the indexed linear memory by the given amount of new memory pages.
///
/// Returns the previous size of the linear memory upon success or -1 upon failure.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
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
}

impl VisitValues for MemoryGrowInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.new_pages);
    }
}

impl VisitValuesMut for MemoryGrowInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.new_pages);
    }
}

/// Returns the current number of pages of the indexed linear memory.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
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
