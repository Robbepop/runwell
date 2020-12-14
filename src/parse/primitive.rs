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
use derive_more::{Display, Error, From};

#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
#[display(fmt = "encountered unsupported Wasm type: {:?}", unsupported)]
pub struct UnsupportedWasmType {
    unsupported: wasmparser::Type,
}

/// An `i32` (32-bit integer), `i64` (64-bit integer),
/// `f32` (32-bit floating point) or `f64` (64-bit floating point) type.
///
/// These are currently the only supported type by the Runwell JIT compiler.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    #[display(fmt = "i32")]
    I32,
    #[display(fmt = "i64")]
    I64,
    #[display(fmt = "f32")]
    F32,
    #[display(fmt = "f64")]
    F64,
}

impl TryFrom<wasmparser::Type> for Type {
    type Error = UnsupportedWasmType;

    fn try_from(ty: wasmparser::Type) -> Result<Self, Self::Error> {
        let result = match ty {
            wasmparser::Type::I32 => Type::I32,
            wasmparser::Type::I64 => Type::I64,
            wasmparser::Type::F32 => Type::F32,
            wasmparser::Type::F64 => Type::F64,
            unsupported => return Err(UnsupportedWasmType { unsupported }),
        };
        Ok(result)
    }
}

/// An `i32` (32-bit integer), `i64` (64-bit integer),
/// `f32` (32-bit floating point) or `f64` (64-bit floating point) value.
///
/// These are currently the only supported type by the Runwell JIT compiler.
#[derive(Debug, Display, From, Copy, Clone, PartialEq)]
pub enum Value {
    #[display(fmt = "i32.const {}", _0)]
    I32(i32),
    #[display(fmt = "i64.const {}", _0)]
    I64(i64),
    #[display(fmt = "f32.const {}", _0)]
    F32(f32),
    #[display(fmt = "f64.const {}", _0)]
    F64(f64),
}

impl Value {
    /// Returns the type of the value.
    pub fn ty(&self) -> Type {
        match self {
            Self::I32(_) => Type::I32,
            Self::I64(_) => Type::I64,
            Self::F32(_) => Type::F32,
            Self::F64(_) => Type::F64,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_display_works() {
        assert_eq!(Type::I32.to_string(), "i32");
        assert_eq!(Type::I64.to_string(), "i64");
        assert_eq!(Type::F32.to_string(), "f32");
        assert_eq!(Type::F64.to_string(), "f64");
    }

    #[test]
    fn value_display_works() {
        assert_eq!(Value::I32(1).to_string(), "i32.const 1");
        assert_eq!(Value::I32(-1).to_string(), "i32.const -1");
        assert_eq!(Value::I64(1).to_string(), "i64.const 1");
        assert_eq!(Value::I64(-1).to_string(), "i64.const -1");
        assert_eq!(Value::F32(1.2).to_string(), "f32.const 1.2");
        assert_eq!(Value::F32(-1.2).to_string(), "f32.const -1.2");
        assert_eq!(Value::F64(1.2).to_string(), "f64.const 1.2");
        assert_eq!(Value::F64(-1.2).to_string(), "f64.const -1.2");
    }
}
