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

use crate::ir::{source::Source, Label, LocalVar, Type};

/// Allocates a number of elements of type `ty` on the program stack.
///
/// # Note
///
/// This is essentially used to model function local variables.
pub struct AllocaOp {
    /// The type of the allocated entity.
    ty: Type,
    /// Parameters for allocating an array of values on the stack.
    ///
    /// A value of `None` means only one value if allocated.
    array: Option<AllocaOpArrayParams>,
}

/// Parameters for `alloca` to indicate allocating multiple elements with specified alignment.
pub struct AllocaOpArrayParams {
    /// The amount of allocated stack variables.
    amount: usize,
    /// The alignment of the allocated stack variables.
    alignment: Option<usize>,
}

/// An SSA phi node.
///
/// Stores the value of any of the matching origins.
/// All listed origins must be direct predecessors of the parent basic block.
///
/// # Note
///
/// - Phi operations cannot occure in the first basic block of a function.
/// - Phi operations may never be preceeded by other non-Phi operations.
///
/// # Examples
///
/// A Phi operation that stores the result into `v0`
/// and determines the stored value in dependence of the
/// preceeding basic block of the actual execution.
/// This will be the value stored in `v1` if predecessor is
/// basic block `bb0` and `v2` if predecessor is basic block `bb1`.
///
/// ```no_compile
/// %v0 = phi i32 [ (%bb0, %v1), (%bb1, %v2) ]
/// ```
pub struct PhiOp {
    /// The local variable binding.
    dst: LocalVar,
    /// The result type of the operation.
    ///
    /// All origins must be of the same type.
    ty: Type,
    /// The origins of the phi operation.
    ///
    /// Must contain at least 2 origins.
    origins: Vec<PhiOpOrigin>,
}

/// An origin of a phi operation.
pub struct PhiOpOrigin {
    /// The label of the origin.
    origin: Label,
    /// The value of the origin.
    src: Source,
}

/// Represents a memory location.
///
/// # Note
///
/// Memory locations are always pointers to actual state.
/// Operations like `alloca`, global variables or static memory
/// represents memory.
/// The `load` and `store` can be used to interact with memory instances.
#[derive(Debug, PartialEq, Eq)]
pub struct Memory(usize);

/// Loads the value stored at the memory location into `dst`.
pub struct LoadOp {
    /// The destination local binding.
    dst: LocalVar,
    /// The memory location of the loaded value.
    src: Memory,
    /// The type of the loaded entity.
    ty: Type,
}

/// Stores the value of `src` into the memory location of `dst`.
pub struct StoreOp {
    /// The destination memory location.
    dst: Memory,
    /// The source local binding.
    src: LocalVar,
    /// The type of the loaded entity.
    ty: Type,
}
