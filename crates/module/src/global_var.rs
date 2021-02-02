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

use core::fmt;
use entity::{DisplayHook, Idx};
use ir::primitive::Type;

/// A global variable declaration.
#[derive(Debug)]
pub struct GlobalVariable {
    ty: Type,
    is_mutable: bool,
}

impl GlobalVariable {
    /// The type of the global variable.
    pub fn ty(&self) -> Type {
        self.ty
    }

    /// Returns `true` if the global variable is mutable.
    pub fn is_mutable(&self) -> bool {
        self.is_mutable
    }
}

/// A global variable entity.
#[derive(Debug, Default)]
pub struct GlobalVariableEntity;

/// The unique index of a global variable.
pub type Global = Idx<GlobalVariableEntity>;

impl DisplayHook for GlobalVariableEntity {
    fn fmt(idx: Global, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "global({})", idx.into_raw())
    }
}
