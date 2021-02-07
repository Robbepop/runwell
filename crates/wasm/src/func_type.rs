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

/// A function type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionType {
    /// The Runwell function type.
    inner: module::FunctionType,
}

impl FunctionType {
    /// Returns the runwell function type.
    pub fn into_inner(self) -> module::FunctionType {
        self.inner
    }
}

impl TryFrom<wasmparser::FuncType> for FunctionType {
    type Error = Error;

    fn try_from(func_type: wasmparser::FuncType) -> Result<Self, Self::Error> {
        let mut builder = module::FunctionType::build();
        for input in func_type.params.iter().copied().map(Type::try_from) {
            let input = input.map(Type::into_inner).map_err(|err| {
                err.with_context(
                    "invalid or unsupported type for function input",
                )
            })?;
            builder.push_input(input);
        }
        for output in func_type.returns.iter().copied().map(Type::try_from) {
            let output = output.map(Type::into_inner).map_err(|err| {
                err.with_context(
                    "invalid or unsupported type for function output",
                )
            })?;
            builder.push_output(output);
        }
        Ok(FunctionType {
            inner: builder.finalize(),
        })
    }
}
