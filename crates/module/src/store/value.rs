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

use derive_more::Display;
use ir::primitive::{FloatType, IntType, Type, F32, F64};

/// A typed runtime value.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RuntimeValue {
    I1(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    F32(F32),
    F64(F64),
}

#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "encountered invalid bit pattern for {}: {:X}", ty, bits)]
pub struct InvalidBitPattern {
    ty: Type,
    bits: u64,
}

impl RuntimeValue {
    /// Converts the bits to the typed runtime value.
    ///
    /// # Errors
    ///
    /// If the bits form an invalid bit pattern for the given type.
    pub fn from_bits(ty: Type, bits: u64) -> Result<Self, InvalidBitPattern> {
        if bits > ty.valid_mask() {
            return Err(InvalidBitPattern { ty, bits })
        }
        let value = match ty {
            Type::Int(IntType::I1) => Self::I1(bits != 0),
            Type::Int(IntType::I8) => Self::I8(bits as _),
            Type::Int(IntType::I16) => Self::I16(bits as _),
            Type::Int(IntType::I32) => Self::I32(bits as _),
            Type::Int(IntType::I64) => Self::I64(bits as _),
            Type::Float(FloatType::F32) => {
                Self::F32(F32::from_bits(bits as _))
            }
            Type::Float(FloatType::F64) => {
                Self::F64(F64::from_bits(bits))
            }
            _ => unimplemented!("pointer types are not yet supported"),
        };
        Ok(value)
    }

    /// Converts the runtime value into a 64-bits representation.
    pub fn into_bits(self) -> u64 {
        match self {
            Self::I1(value) => value as _,
            Self::I8(value) => u64::from(value as u8),
            Self::I16(value) => u64::from(value as u16),
            Self::I32(value) => u64::from(value as u32),
            Self::I64(value) => value as u64,
            Self::F32(value) => u64::from(value.bits()),
            Self::F64(value) => value.bits(),
        }
    }
}

macro_rules! impl_from_primitive {
    ( $( impl From<$variant_type:ty> for RuntimeValue::$variant_ident:ident );* $(;)? ) => {
        $(
            impl From<$variant_type> for RuntimeValue {
                fn from(value: $variant_type) -> Self {
                    Self::$variant_ident(value)
                }
            }
        )*
    };
}
impl_from_primitive! {
    impl From<bool> for RuntimeValue::I1;
    impl From<i8> for RuntimeValue::I8;
    impl From<i16> for RuntimeValue::I16;
    impl From<i32> for RuntimeValue::I32;
    impl From<i64> for RuntimeValue::I64;
    impl From<F32> for RuntimeValue::F32;
    impl From<F64> for RuntimeValue::F64;
}

macro_rules! impl_from_unsigned_primitive {
    ( $( impl From<$unsigned_type:ty> for RuntimeValue::$variant_ident:ident { _ as $variant_type:ty } )* ) => {
        $(
            impl From<$unsigned_type> for RuntimeValue {
                fn from(value: $unsigned_type) -> Self {
                    Self::$variant_ident(value as $variant_type)
                }
            }
        )*
    };
}
impl_from_unsigned_primitive! {
    impl From<u8> for RuntimeValue::I8 { _ as i8 }
    impl From<u16> for RuntimeValue::I16 { _ as i16 }
    impl From<u32> for RuntimeValue::I32 { _ as i32 }
    impl From<u64> for RuntimeValue::I64 { _ as i64 }
}

macro_rules! impl_as_primitive {
    ( $(
        $( #[$docs:meta] ),*
        fn $fn_name:ident($variant_name:ident) -> $variant_type:ty
    );* $(;)? ) => {
        impl RuntimeValue {
            $(
                $(
                    #[$docs]
                )*
                pub fn $fn_name(self) -> Option<$variant_type> {
                    if let Self::$variant_name(value) = self {
                        return Some(value)
                    }
                    None
                }
            )*
        }
    };
}
impl_as_primitive! {
    /// Returns the `bool`value or `None`if the type is not `bool`.
    fn as_bool(I1) -> bool;

    /// Returns the `i8` value or `None` if the type is not `i8`.
    fn as_i8(I8) -> i8;

    /// Returns the `i16` value or `None` if the type is not `i16`.
    fn as_i16(I16) -> i16;

    /// Returns the `i32` value or `None` if the type is not `i32`.
    fn as_i32(I32) -> i32;

    /// Returns the `i64` value or `None` if the type is not `i64`.
    fn as_i64(I64) -> i64;

    /// Returns the `f32` value or `None` if the type is not `f32`.
    fn as_f32(F32) -> F32;

    /// Returns the `f64` value or `None` if the type is not `f64`.
    fn as_f64(F64) -> F64;
}

impl RuntimeValue {
    /// Creates a default value for the given value type.
    pub fn default(value_type: Type) -> Self {
        match value_type {
            Type::Ptr => Self::I32(Default::default()),
            Type::Int(IntType::I1) => Self::I1(false),
            Type::Int(IntType::I8) => Self::I8(Default::default()),
            Type::Int(IntType::I16) => Self::I16(Default::default()),
            Type::Int(IntType::I32) => Self::I32(Default::default()),
            Type::Int(IntType::I64) => Self::I64(Default::default()),
            Type::Float(FloatType::F32) => {
                Self::F32(Default::default())
            }
            Type::Float(FloatType::F64) => {
                Self::F64(Default::default())
            }
        }
    }

    /// Returns the value type of the runtime value.
    pub fn value_type(self) -> Type {
        match self {
            Self::I1(_) => Type::Int(IntType::I1),
            Self::I8(_) => Type::Int(IntType::I8),
            Self::I16(_) => Type::Int(IntType::I16),
            Self::I32(_) => Type::Int(IntType::I32),
            Self::I64(_) => Type::Int(IntType::I64),
            Self::F32(_) => Type::Float(FloatType::F32),
            Self::F64(_) => Type::Float(FloatType::F64),
        }
    }
}
