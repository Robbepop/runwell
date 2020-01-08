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
    parse::operator::IntType as Type,
};

/// Loads the constant value.
///
/// # Example
///
/// Loads the constant `42` of type `i32` into `%1`.
///
/// ```no_compile
/// %1 <- i32.const 42
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstOp {
    /// The destination value to store the constant value.
    dst: ValueId,
    /// The constant value.
    val: ConstValue,
    /// The type of the constant value.
    ty: Type,
}

/// A constant value.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstValue {
    /// An constant value of type `i32`.
    I32(i32),
    /// An constant value of type `i64`.
    I64(i64),
}

impl DestinationId for ConstOp {
    fn destination_id(&self) -> Option<ValueId> {
        Some(self.dst)
    }
}
