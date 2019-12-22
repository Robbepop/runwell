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
    ir::ValueId,
    parse::{LocalVariableId, GlobalVariableId},
};
use wasmparser::Type;
use derive_more::From;

/// A local or global variable identifier.
#[derive(From)]
pub enum VariableId {
    /// A local variable ID.
    Local(LocalVariableId),
    /// A global variable ID.
    Global(GlobalVariableId),
}

/// A local variable declaration.
///
/// # Example
///
/// ```no_compile
/// %1 <- i32.local
/// %2 <- i64.local
/// ```
pub struct LocalOp {
    /// The ID of the local variable.
    id: LocalVariableId,
    /// The type of the local variable.
    ty: Type,
}

/// Returns the value of a local or global variable.
///
/// # Example
///
/// Get the local variable identified by `0` of type `i32` and store the result
/// into `%1`.
///
/// ```no_compile
/// %1 <- i32.get local 0
/// ```
///
/// Get the global variable identified by `1` of type `i64` and store the result
/// into `%2`.
///
/// ```no_compile
/// %2 <- i64.get global 1
/// ```
pub struct GetOp {
    /// The ID of the local variable.
    id: VariableId,
    /// The type of the loaded value.
    ty: Type,
}

/// Sets the value of a local or global variable.
///
/// # Example
///
/// Set the value of the local variable identified by `0` of type `i32`
/// to `%1`.
///
/// ```no_compile
/// i32.set local 0 <- %1
/// ```
///
/// Set the value of the global variable identified by `1` of type `i64`
/// to `%2`.
///
/// ```no_compile
/// i64.set global 1 <- %2
/// ```
pub struct SetOp {
    /// The ID of the local variable.
    id: VariableId,
    /// The type of the stored value.
    val: ValueId,
}
