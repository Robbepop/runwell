// Copyright 2021 Robin Freyler
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
    primitive::{Type, Value},
    ReplaceValue,
    VisitValues,
    VisitValuesMut,
};
use derive_more::Display;

/// Choose a value based on a condition without IR-level branching.
///
/// # Note
///
/// This might result in branching operations when translated to
/// machine code.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
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

    /// Returns the value of the condition.
    pub fn condition(&self) -> Value {
        self.condition
    }

    /// Returns the type of the operands.
    pub fn ty(&self) -> Type {
        self.ty
    }

    /// Returns the value returned if the condition evaluates to `true`.
    pub fn true_value(&self) -> Value {
        self.value_true
    }

    /// Returns the value returned if the condition evaluates to `false`.
    pub fn false_value(&self) -> Value {
        self.value_false
    }
}

impl VisitValues for SelectInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        let _ = visitor(self.condition)
            && visitor(self.value_true)
            && visitor(self.value_false);
    }
}

impl VisitValuesMut for SelectInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        let _ = visitor(&mut self.condition)
            && visitor(&mut self.value_true)
            && visitor(&mut self.value_false);
    }
}

impl ReplaceValue for SelectInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.condition)
            || replace(&mut self.value_true)
            || replace(&mut self.value_false)
    }
}
