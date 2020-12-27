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

//! Runwell primitive types and constant values.
//!
//! Unlike Wasm the Runwell JIT supports 8-bit and 16-bit integer types.
//! This is to generalize certain compound Wasm operations such as `i32.load8_u`
//! that first load an 8-bit integer from the given address and then zero-extends it
//! to a 32-bit integer value.

use crate::parse2::{self, F32, F64};
use derive_more::{Display, From};

/// Any Runwell supported primitive type.
#[derive(Debug, Display, From, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Int(IntType),
    Float(FloatType),
}

impl From<parse2::Type> for Type {
    fn from(ty: parse2::Type) -> Self {
        match ty {
            parse2::Type::I32 => Self::Int(IntType::I32),
            parse2::Type::I64 => Self::Int(IntType::I64),
            parse2::Type::F32 => Self::Float(FloatType::F32),
            parse2::Type::F64 => Self::Float(FloatType::F64),
        }
    }
}

impl Type {
    /// Returns the bit width of the type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::Int(int_type) => int_type.bit_width(),
            Self::Float(float_type) => float_type.bit_width(),
        }
    }
}

/// Any fixed-size integer type.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntType {
    #[display(fmt = "i8")]
    I8,
    #[display(fmt = "i16")]
    I16,
    #[display(fmt = "i32")]
    I32,
    #[display(fmt = "i64")]
    I64,
}

impl IntType {
    /// Returns the bit width of the fixed-size integer type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 => 64,
        }
    }
}

/// Any floating point number type.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatType {
    #[display(fmt = "f32")]
    F32,
    #[display(fmt = "f64")]
    F64,
}

impl FloatType {
    /// Returns the bit width of the floating point number type.
    pub fn bit_width(&self) -> u32 {
        match self {
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }
}

/// A Runwell constant value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Const {
    Int(IntConst),
    Float(FloatConst),
}

impl Const {
    /// Returns the type of the constant value.
    pub fn ty(&self) -> Type {
        match self {
            Self::Int(int_const) => int_const.ty(),
            Self::Float(float_const) => float_const.ty(),
        }
    }
}

/// A constant fixed-size integer value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntConst {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
}

impl IntConst {
    /// Returns the type of the constant fixed-size integer.
    pub fn ty(&self) -> Type {
        match self {
            Self::I8(_) => IntType::I8.into(),
            Self::I16(_) => IntType::I16.into(),
            Self::I32(_) => IntType::I32.into(),
            Self::I64(_) => IntType::I64.into(),
        }
    }
}

/// A constant floating point number value.
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatConst {
    F32(F32),
    F64(F64),
}

impl FloatConst {
    /// Returns the type of the constant floating point number.
    pub fn ty(&self) -> Type {
        match self {
            Self::F32(_) => FloatType::F32.into(),
            Self::F64(_) => FloatType::F64.into(),
        }
    }
}
