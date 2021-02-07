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

use super::Error;
use core::convert::TryFrom;
use derive_more::{Display, Error, From};
use ir::primitive as runwell;

/// An error that occured while operating on Wasm primitives.
#[derive(Debug, Display, Error, From, PartialEq, Eq, Hash)]
pub enum PrimitiveError {
    #[display(fmt = "encountered unsupported Wasm type: {:?}", unsupported)]
    UnsupportedWasmType { unsupported: wasmparser::Type },
}

/// A Wasm translated Runwell type.
pub struct Type {
    inner: runwell::Type,
}

impl Type {
    /// Returns the runwell Type.
    pub fn into_inner(self) -> runwell::Type {
        self.inner
    }
}

impl TryFrom<wasmparser::Type> for Type {
    type Error = Error;

    fn try_from(ty: wasmparser::Type) -> Result<Self, Self::Error> {
        let ty = match ty {
            wasmparser::Type::I32 => runwell::IntType::I32.into(),
            wasmparser::Type::I64 => runwell::IntType::I64.into(),
            wasmparser::Type::F32 => runwell::FloatType::F32.into(),
            wasmparser::Type::F64 => runwell::FloatType::F64.into(),
            wasmparser::Type::V128
            | wasmparser::Type::FuncRef
            | wasmparser::Type::ExternRef
            | wasmparser::Type::ExnRef
            | wasmparser::Type::Func
            | wasmparser::Type::EmptyBlockType => {
                return Err(PrimitiveError::UnsupportedWasmType {
                    unsupported: ty,
                })
                .map_err(Into::into)
            }
        };
        Ok(Self { inner: ty })
    }
}

/// A Wasm translated Runwell constant value.
pub struct Const {
    inner: runwell::Const,
}

impl Const {
    /// Returns the runwell constant value.
    pub fn into_inner(self) -> runwell::Const {
        self.inner
    }
}

impl From<i32> for Const {
    fn from(value: i32) -> Self {
        Self {
            inner: runwell::IntConst::I32(value).into(),
        }
    }
}

impl From<i64> for Const {
    fn from(value: i64) -> Self {
        Self {
            inner: runwell::IntConst::I64(value).into(),
        }
    }
}

impl From<wasmparser::Ieee32> for Const {
    fn from(value: wasmparser::Ieee32) -> Self {
        Self {
            inner: runwell::F32::from_bits(value.bits()).into(),
        }
    }
}

impl From<wasmparser::Ieee64> for Const {
    fn from(value: wasmparser::Ieee64) -> Self {
        Self {
            inner: runwell::F64::from_bits(value.bits()).into(),
        }
    }
}
