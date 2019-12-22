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

use crate::{ir::ValueId, parse::LinearMemoryId};

/// The Wasm `memory.grow` operation in SSA form.
///
/// # Example
///
/// Grows linear memory identified by `0` by the amount of bytes equal to
/// the value stored at `%1`.
///
/// ```no_compile
/// memory.grow memory 0 <- %1
/// ```
pub struct MemoryGrowOp {
    /// The identifier of the linear memory to grow.
    memory: LinearMemoryId,
    /// The amount of bytes to grow the linear memory buffer.
    grow_by: ValueId,
}

/// The Wasm `memory.size` operation in SSA form.
///
/// # Example
///
/// Returns the size of the memory identified by `0` to `%1`.
///
/// ```no_compile
/// %1 <- memory.size memory 0
/// ```
pub struct MemorySizeOp {
    /// The value to store the result to.
    val: ValueId,
    /// The identifier of the linear memory.
    memory: LinearMemoryId,
}
