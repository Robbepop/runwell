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

use crate::ir::primitive::{Type, Value};
use derive_more::Display;

/// Choose a value based on a condition without IR-level branching.
///
/// # Note
///
/// This might result in branching operations when translated to
/// machine code.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(
    fmt = "select condition {}, true {}, false {}",
    condition,
    value_true,
    value_false
)]
pub struct SelectInstr {
    /// The condition value.
    condition: Value,
    /// The type of the returned value.
    ty: Type,
    /// The value if `condition` evaluates to `true`.
    value_true: Value,
    /// The value if `condition` evaluates to `false`.
    value_false: Value,
}

impl SelectInstr {
    /// Creates a new select operation.
    pub fn new(
        condition: Value,
        ty: Type,
        value_true: Value,
        value_false: Value,
    ) -> Self {
        Self {
            condition,
            ty,
            value_true,
            value_false,
        }
    }
}
