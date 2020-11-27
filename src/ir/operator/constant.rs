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

use crate::parse::operator::IntType as Type;

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
    /// The constant value.
    val: ConstValue,
}

/// A constant value.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstValue {
    /// An constant value of type `i32`.
    I32(i32),
    /// An constant value of type `i64`.
    I64(i64),
}

impl From<i32> for ConstOp {
    fn from(val: i32) -> Self {
        Self {
            val: ConstValue::I32(val),
        }
    }
}

impl From<i64> for ConstOp {
    fn from(val: i64) -> Self {
        Self {
            val: ConstValue::I64(val),
        }
    }
}

impl ConstOp {
    /// Returns the type of the constant value.
    pub fn ty(&self) -> Type {
        match self.val {
            ConstValue::I32(_) => Type::I32,
            ConstValue::I64(_) => Type::I64,
        }
    }
}
