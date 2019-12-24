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

use crate::{ir::ValueId, parse::operator::IntType as Type};

/// Choose a value based on a condition without IR-level branching.
///
/// # Note
///
/// This might result in branching operations when translated to
/// machine code.
///
/// # Example
///
/// Store `%2` of type `i32` in `%0` if the value in `%1` is `true` or store
/// `%3` of type `i32` in `%0` otherwise.
///
/// ```no_compile
/// %0 <- i32.select %1 <- %2 or %3
/// ```
pub struct SelectOp {
    /// The condition value.
    condition: ValueId,
    /// The type of the resulting value.
    ty: Type,
    /// The value if `condition` evaluates to `true`.
    true_val: ValueId,
    /// The value if `condition` evaluates to `false`.
    false_val: ValueId,
}