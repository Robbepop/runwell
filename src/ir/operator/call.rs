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
    ir::{operator::DestinationId, CallParam, ValueId},
    parse::{FunctionId, TableId},
};

/// Calls a function.
///
/// Returns back to the caller after execution.
///
/// # Examples
///
/// Calls function identified by `42` with parameters `%1` of type `i32`
/// and `%5` of type `i64`.
///
/// ```no_compile
/// %dst <- call fn 42 params [ i32 %1, i64 %5 ]
/// ```
pub struct CallOp {
    /// The destination value.
    dst: ValueId,
    /// The identified of the called function.
    id: FunctionId,
    /// The parameters of the function call.
    params: Vec<CallParam>,
}

impl DestinationId for CallOp {
    fn destination_id(&self) -> Option<ValueId> {
        Some(self.dst)
    }
}

/// Calls a function indirectly through a table.
///
/// Returns back to the caller after execution.
///
/// # Example
///
/// Calls function identified by `123` indirectly through table identified by
/// `2` with offset of `5` and parameters of `%2` of type `i64` and `%4` of
/// type `i64`.
///
/// ```no_compile
/// %dst <- call.indirect table 2 offset 5 params [ i64 %2, i64 %4 ]
/// ```
pub struct CallIndirectOp {
    /// The destination value.
    dst: ValueId,
    /// The table ID for receiving the indirectly called function pointers.
    table_id: TableId,
    /// The offset within the table.
    table_offset: usize,
    /// The parameters of the function call.
    params: Vec<CallParam>,
}

impl DestinationId for CallIndirectOp {
    fn destination_id(&self) -> Option<ValueId> {
        Some(self.dst)
    }
}
