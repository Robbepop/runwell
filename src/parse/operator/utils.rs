// Copyright 2019 Robin Freyler
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

/// A local variable ID.
///
/// Used to access local variables of Wasm functions.
#[derive(Debug)]
pub struct LocalId(pub(super) usize);


/// The extended set of integer types.
///
/// # Note
///
/// Required for generic `load` and `store` as well as for
/// conversion routines.
#[derive(Debug, Copy, Clone)]
pub enum ExtIntType {
    /// 8-bit integer type.
    I8,
    /// 16-bit integer type.
    I16,
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

impl ExtIntType {
    /// Returns `true` if `self` type is extendable to the `dst` type.
    pub fn is_extendable_to(self, dst: IntType) -> bool {
        self.width() < dst.width()
    }

    /// Returns the number of bytes used to represent a value of the type.
    pub fn width(self) -> usize {
        match self {
            ExtIntType::I8 => 1,
            ExtIntType::I16 => 2,
            ExtIntType::I32 => 3,
            ExtIntType::I64 => 4,
        }
    }
}

impl From<IntType> for ExtIntType {
    fn from(int_ty: IntType) -> Self {
        match int_ty {
            IntType::I32 => ExtIntType::I32,
            IntType::I64 => ExtIntType::I64,
        }
    }
}

/// A Wasm integer type.
#[derive(Debug, Copy, Clone)]
pub enum IntType {
    /// 32-bit integer type.
    I32,
    /// 64-bit integer type.
    I64,
}

impl IntType {
    /// Returns `true` if `self` is truncatable to the `dst` type.
    pub fn is_truncatable_to(self, dst: ExtIntType) -> bool {
        self.width() > dst.width()
    }

    /// Returns the number of bytes used to represent a value of the type.
    pub fn width(self) -> usize {
        match self {
            IntType::I32 => 4,
            IntType::I64 => 8,
        }
    }
}

/// Either signed or unsigned.
#[derive(Debug, Copy, Clone)]
pub enum Signedness {
    Unsigned,
    Signed,
}
