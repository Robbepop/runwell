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

use core::convert::TryFrom;
use crate::parse::ParseError;

/// An `i32` or `i64` type.
///
/// These are currently the only supported type by the Runwell JIT compiler.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    I32,
    I64,
}

impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::I32 => write!(f, "i32"),
            Self::I64 => write!(f, "i64"),
        }
    }
}

impl TryFrom<wasmparser::Type> for Type {
    type Error = ParseError;

    fn try_from(ty: wasmparser::Type) -> Result<Self, Self::Error> {
        let result = match ty {
            wasmparser::Type::I32 => Type::I32,
            wasmparser::Type::I64 => Type::I64,
            unsupported => {
                return Err(ParseError::UnsupportedType(format!(
                    "{:?}",
                    unsupported
                )))
            }
        };
        Ok(result)
    }
}

/// An `i32` or `i64` value.
///
/// These are currently the only supported type by the Runwell JIT compiler.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Value {
    I32(i32),
    I64(i64),
}

impl core::fmt::Display for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::I32(value) => write!(f, "i32.const {}", value),
            Self::I64(value) => write!(f, "i64.const {}", value),
        }
    }
}
