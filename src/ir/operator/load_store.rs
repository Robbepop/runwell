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

use crate::{
    ir::Binding,
    parse::{LinearMemoryId, Type},
};

/// A local variable declaration.
///
/// Has a type and a number of allocated local elements.
///
/// # Example
///
/// - Allocates a single `i32` local variable and stores it as `%1`.
///   Note that `%1` refers to a pointer to an `i32`.
///
/// ```no_compile
/// %1 <- local i32 len 1
/// ```
///
/// - Allocates an array of 4 `i64` local variables and store them as `%1`.
///   Note that `%1` refers to a pointer to `i64`.
///
/// ```no_compile
/// %1 <- local i64 len 4
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalOp {
    /// The type of the local variable.
    ty: Type,
    /// The number of local elements.
    len: usize,
}

impl LocalOp {
    /// Allocates a single local elements of given type.
    pub fn single(ty: Type) -> Self {
        Self { ty, len: 1 }
    }

    /// Allocates an array of local elements of given type and length.
    pub fn array(ty: Type, len: usize) -> Self {
        Self { ty, len }
    }
}

/// Specifies the kind of memory location.
///
/// # Note
///
/// Mainly used by optimizer in order to produce better code.
/// Local variable accesses can potentially be reordered.
/// Optimizers can assume that all memory spaces are disjunct from each other.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MemoryKind {
    /// A function local variable memory location.
    Local,
    /// A global variable memory location.
    Global,
    /// A linear memory location.
    LinearMemory(LinearMemoryId),
}

impl MemoryKind {
    /// Creates a default linear memory kind.
    fn default_memory() -> Self {
        Self::LinearMemory(Default::default())
    }
}

/// Loads the value stored at the memory location.
///
/// # Note
///
/// Allows to operate on `local`, `global` and from any linear memory region.
///
/// # Example
///
///
/// - Load the value of type `i32` at index `%0` with alignment of 2 from
///   linear memory 0 and store it as `%1`.
///
/// ```no_compile
/// %1 <- i32.load memory 0 at %0 align 2
/// ```
///
/// - Load the value of type `i64` at local index `%0` with alignment of 2^3
///   (= 8) and store it as `%1`.
///
/// ```no_compile
/// %1 <- i64.load local at %0 align 3
/// ```
///
/// - Load the value of type `i32` at global index `%0` with alignment of 2^2
///   (= 4) and store it as `%1`.
///
/// ```no_compile
/// %1 <- i32.load global at %0 align 2
/// ```
///
/// - Loads the local variables with different offsets into their respective
///   bindings.
///
/// ```no_compile
/// %0 <- alloc i32 2
/// %1 <- load i32 local at %0 align 2
/// %2 <- const i32 1
/// %3 <- getelemptr %0 %2
/// %4 <- load i32 local at %3 align 2
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LoadOp {
    /// The type of the memory where the value is being loaded.
    kind: MemoryKind,
    /// The type of the loaded value.
    ty: Type,
    /// The index where the load is performed.
    at: Binding,
}

impl LoadOp {
    /// Creates a new load operation to load the value of a local variable.
    pub fn load_local(ty: Type, at: Binding) -> Self {
        Self {
            kind: MemoryKind::Local,
            ty,
            at,
        }
    }
}

/// Stores the value of `src` into the memory location of `dst`.
///
/// # Example
///
/// - Store the value stored at `%1` of type `i64` with an alignment of
/// 2^3 (= 8) into linear memory 0.
///
/// ```no_compile
/// i64.store memory 0 value %1 at %2 align 3
/// ```
///
/// - Store the local value stored at `%1` of type `i32` with an alignment of
///   2^2 (= 4).
///
/// ```no_compile
/// i32.store local value %1 at %2 align 2
/// ```
///
/// - Store the global value stored at `%1` of type `i32` with an alignment of
///   2^2 (= 4).
///
/// ```no_compile
/// i32.store global value %1 at %2 align 2
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StoreOp {
    /// The type of the memory where the value is being stored.
    kind: MemoryKind,
    /// The type of the stored value.
    ty: Type,
    /// The index where the store is performed.
    dst: Binding,
    /// The value that is being stored.
    src: Binding,
}

impl StoreOp {
    /// Creates a new store operation to store a value into a local variable.
    pub fn store_local(ty: Type, dst: Binding, src: Binding) -> Self {
        Self {
            kind: MemoryKind::Local,
            ty,
            dst,
            src,
        }
    }
}
