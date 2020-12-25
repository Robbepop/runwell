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

use crate::ir::{Const, Type};
use derive_more::Display;

#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "const {}", const_value)]
pub struct ConstInstr {
    const_value: Const,
}

impl ConstInstr {
    /// Creates a new constant instruction.
    pub fn new(const_value: Const) -> Self {
        Self { const_value }
    }

    /// Returns the type of the constant value of the constant instruction.
    pub fn ty(&self) -> Type {
        self.const_value.ty()
    }

    /// Returns the constant value of the constant instruction.
    pub fn const_value(&self) -> &Const {
        &self.const_value
    }
}
