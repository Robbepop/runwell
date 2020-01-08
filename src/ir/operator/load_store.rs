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

use crate::{
    ir::{operator::DestinationId, ValueId},
    parse::{operator::IntType, LinearMemoryId},
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

/// The location within the linear memory and alignment.
pub struct MemoryParams {
    /// The memory location of the loaded value.
    memory: Option<LinearMemoryId>,
    /// The offset within the linear memory of the loaded value.
    offset: usize,
    /// The alignment of the loaded value.
    alignment: Option<usize>,
}

/// Loads the value stored at the memory location into `dst`.
///
/// # Example
///
/// Load the value of type `i32` at offset `12` with alignment `2` of
/// memory identified by `0` into `%1`.
///
/// ```no_compile
/// %1 <- i32.load memory 0 at 12 alignment 2
/// %1 <- i32.load at 12 alignment 2          ;; memory 0 is implicit
/// %1 <- i32.load at 12                      ;; alignment is deferred from type
/// ```
pub struct LoadOp {
    /// The destination value.
    dst: ValueId,
    /// The type of the loaded entity.
    ty: IntType,
    /// The linear memory location and alignment.
    memory: MemoryParams,
}

    }
}

/// Stores the value of `src` into the memory location of `dst`.
///
/// # Example
///
/// Stores the value stored at `%1` of type `i64` at offset `0` with
/// alignmnet `4` into memory identified by `0`.
///
/// ```no_compile
/// i64.store memory 0 at 42 alignment 4 <- %1
/// ```
pub struct StoreOp {
    /// The source local binding.
    src: ValueId,
    /// The type of the stored value.
    ty: IntType,
    /// The linear memory location and alignment.
    memory: MemoryParams,
}

    }
}
