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

use super::{Error, Type};
use core::convert::TryFrom;

/// A global variable declaration.
#[derive(Debug)]
pub struct GlobalVariable {
    /// The internal Runwell translated global variable.
    inner: module::GlobalVariable,
}

impl GlobalVariable {
    /// Returns the inner Runwell global variable.
    pub fn into_inner(self) -> module::GlobalVariable {
        self.inner
    }
}

impl TryFrom<wasmparser::GlobalType> for GlobalVariable {
    type Error = Error;

    fn try_from(
        global_type: wasmparser::GlobalType,
    ) -> Result<Self, Self::Error> {
        let content_type = Type::try_from(global_type.content_type)
            .map_err(Error::from)
            .map_err(|err| {
                err.with_context("unsupported type for global variable")
            })?;
        let is_mutable = global_type.mutable;
        Ok(Self {
            inner: module::GlobalVariable::new(
                content_type.into_inner(),
                is_mutable,
            ),
        })
    }
}
