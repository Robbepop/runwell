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

use super::{ParseError, Type};
use core::convert::TryFrom;

/// A global variable declaration.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalVariable {
    /// The type of the global variable.
    content_type: Type,
    /// Is `true` if the global variable is declared as mutable.
    mutable: bool,
}

impl GlobalVariable {
    /// Returns the type of the global variable.
    pub fn ty(&self) -> &Type {
        &self.content_type
    }

    /// Returns `true` if `self` is mutable.
    pub fn is_mutable(self) -> bool {
        self.mutable
    }
}

impl TryFrom<wasmparser::GlobalType> for GlobalVariable {
    type Error = ParseError;

    fn try_from(
        global_type: wasmparser::GlobalType,
    ) -> Result<Self, Self::Error> {
        let content_type = Type::try_from(global_type.content_type)
            .map_err(ParseError::from)
            .map_err(|err| {
                err.with_context("unsupported type for global variable")
            })?;
        let mutable = global_type.mutable;
        Ok(Self {
            content_type,
            mutable,
        })
    }
}
