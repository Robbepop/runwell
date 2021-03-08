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

use crate::InterpretationError;

#[rustfmt::skip]
mod conv {
    pub fn reg_to_i8(reg: u64) -> i8 { reg as u8 as i8 }
    pub fn reg_to_i16(reg: u64) -> i16 { reg as u16 as i16 }
    pub fn reg_to_i32(reg: u64) -> i32 { reg as u32 as i32 }
    pub fn reg_to_i64(reg: u64) -> i64 { reg as u64 as i64 }
    pub fn reg_to_u8(reg: u64) -> u8 { reg as u8 }
    pub fn reg_to_u16(reg: u64) -> u16 { reg as u16 }
    pub fn reg_to_u32(reg: u64) -> u32 { reg as u32 }
    pub fn reg_to_u64(reg: u64) -> u64 { reg }
    pub fn i8_to_reg(val: i8) -> u64 { val as u8 as u64 }
    pub fn i16_to_reg(val: i16) -> u64 { val as u16 as u64 }
    pub fn i32_to_reg(val: i32) -> u64 { val as u32 as u64 }
    pub fn i64_to_reg(val: i64) -> u64 { val as u64 }
    pub fn u8_to_reg(val: u8) -> u64 { val as u64 }
    pub fn u16_to_reg(val: u16) -> u64 { val as u64 }
    pub fn u32_to_reg(val: u32) -> u64 { val as u64 }
    pub fn u64_to_reg(val: u64) -> u64 { val }
}

/// Trait used to streamline operations on primitive types.
pub trait PrimitiveInteger: Copy {
    fn from_reg(reg: u64) -> Self;
    fn into_reg(self) -> u64;
}

/// Trait used to streamline division operations on primitive integer types.
pub trait PrimitiveIntegerDivision: PrimitiveInteger {
    fn checked_div(self, rhs: Self) -> Result<Self, InterpretationError>;
    fn checked_rem(self, rhs: Self) -> Result<Self, InterpretationError>;
}

macro_rules! impl_primitive_integer_for {
    ( $( ($type:ty, $reg_to_val:ident, $val_to_reg:ident) ),* $(,)? ) => {
        $(
            impl PrimitiveInteger for $type {
                fn from_reg(reg: u64) -> Self { conv::$reg_to_val(reg) }
                fn into_reg(self) -> u64 { conv::$val_to_reg(self) }
            }

            impl PrimitiveIntegerDivision for $type {
                fn checked_div(self, rhs: Self) -> Result<Self, InterpretationError> {
                    self.checked_div(rhs).ok_or(InterpretationError::DivisionByZero)
                }
                fn checked_rem(self, rhs: Self) -> Result<Self, InterpretationError> {
                    self.checked_rem(rhs).ok_or(InterpretationError::DivisionByZero)
                }
            }
        )*
    };
}
impl_primitive_integer_for! {
    ( i8, reg_to_i8 , i8_to_reg ),
    (i16, reg_to_i16, i16_to_reg),
    (i32, reg_to_i32, i32_to_reg),
    (i64, reg_to_i64, i64_to_reg),
    ( u8, reg_to_u8 , u8_to_reg ),
    (u16, reg_to_u16, u16_to_reg),
    (u32, reg_to_u32, u32_to_reg),
    (u64, reg_to_u64, u64_to_reg),
}

/// 1-bit integer type.
///
/// Used to implement `PrimitiveInteger` trait so that it can be used on a subset
/// of the available integer instructions.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct I1 {
    value: bool,
}

impl I1 {
    /// Creates a new `I1` value from the given `bool`.
    pub fn new(value: bool) -> Self {
        Self { value }
    }

    /// Extends the `I1` value to an `i8` value.
    pub fn extend_to_i8(self) -> i8 {
        -(self.value as i8)
    }

    /// Extends the `I1` value to an `i16` value.
    pub fn extend_to_i16(self) -> i16 {
        -(self.value as i16)
    }

    /// Extends the `I1` value to an `i32` value.
    pub fn extend_to_i32(self) -> i32 {
        -(self.value as i32)
    }

    /// Extends the `I1` value to an `i64` value.
    pub fn extend_to_i64(self) -> i64 {
        -(self.value as i64)
    }
}

impl PrimitiveInteger for I1 {
    fn from_reg(reg: u64) -> Self {
        debug_assert!(reg <= 1);
        I1 { value: reg != 0 }
    }

    fn into_reg(self) -> u64 {
        self.value as u64
    }
}

impl core::ops::BitAnd for I1 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new(self.value & rhs.value)
    }
}

impl core::ops::BitOr for I1 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::new(self.value | rhs.value)
    }
}

impl core::ops::BitXor for I1 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::new(self.value ^ rhs.value)
    }
}
