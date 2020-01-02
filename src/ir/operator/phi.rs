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
    ir::{operator::DestinationId, BlockId, ValueId},
    parse::operator::IntType as Type,
};

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
/// A Phi operation that stores the result into `%0`
/// and determines the stored value in dependence of the
/// preceeding basic block of the actual execution.
/// This will be the value stored in `%1` if predecessor is
/// basic block `0` and `%2` if predecessor is basic block `1`.
///
/// ```no_compile
/// %0 <- i32.phi [ %1 <- block 0, %2 <- block 1 ]
/// ```
pub struct PhiOp {
    /// The local variable binding.
    dst: ValueId,
    /// The result type of the operation.
    ///
    /// All origins must be of the same type.
    ty: Type,
    /// The origins of the phi operation.
    ///
    /// Must contain at least 2 origins.
    origins: Vec<PhiOpOrigin>,
}

impl DestinationId for PhiOp {
    fn destination_id(&self) -> Option<ValueId> {
        Some(self.dst)
    }
}

/// An origin of a phi operation.
pub struct PhiOpOrigin {
    /// The block of the origin.
    origin: BlockId,
    /// The value of the origin.
    src: ValueId,
}
