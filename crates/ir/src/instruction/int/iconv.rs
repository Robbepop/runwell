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

use crate::primitive::{FloatType, IntType, Value};
use derive_more::Display;

/// Truncates the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be greater than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "itruncate {} -> {}, src {}", src_type, dst_type, src)]
pub struct TruncateIntInstr {
    src_type: IntType,
    dst_type: IntType,
    src: Value,
}

impl TruncateIntInstr {
    /// Creates a new truncate instruction truncating src from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be greater than the bit width of the destination type.
    pub fn new(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        assert!(src_type.bit_width() > dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source type of the truncate instruction.
    pub fn src_type(&self) -> IntType {
        self.src_type
    }

    /// Returns the destination type of the truncate instruction.
    pub fn dst_type(&self) -> IntType {
        self.dst_type
    }

    /// Returns the source of the instruction that is to be extended.
    pub fn src(&self) -> Value {
        self.src
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.src)
    }
}

/// Extends the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be less than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(
    fmt = "{}extend {} -> {}, src {}",
    "if self.signed { 's' } else { 'u' }",
    src_type,
    dst_type,
    src
)]
pub struct ExtendIntInstr {
    signed: bool,
    src_type: IntType,
    dst_type: IntType,
    src: Value,
}

impl ExtendIntInstr {
    /// Creates a new extend instruction extending src from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be less than the bit width of the destination type.
    pub fn new(
        signed: bool,
        src_type: IntType,
        dst_type: IntType,
        src: Value,
    ) -> Self {
        assert!(src_type.bit_width() > dst_type.bit_width());
        Self {
            signed,
            src_type,
            dst_type,
            src,
        }
    }

    /// Creates a new zero-extend instruction extending src from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be less than the bit width of the destination type.
    pub fn zext(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        Self::new(false, src_type, dst_type, src)
    }

    /// Creates a new sign-extend instruction extending src from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be less than the bit width of the destination type.
    pub fn sext(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        Self::new(true, src_type, dst_type, src)
    }

    /// Returns the source type of the truncate instruction.
    pub fn src_type(&self) -> IntType {
        self.src_type
    }

    /// Returns the destination type of the truncate instruction.
    pub fn dst_type(&self) -> IntType {
        self.dst_type
    }

    /// Returns the source of the instruction that is to be extended.
    pub fn src(&self) -> Value {
        self.src
    }

    /// Returns `true` if the source is treated as a signed integer.
    ///
    /// - `true`: `sign-extension`
    /// - `false`: `zero-extension`
    pub fn is_signed(&self) -> bool {
        self.signed
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.src)
    }
}

/// Instruction to convert an integer into a floating point number.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(
    fmt = "{}convert {} -> {}, src {}",
    "if self.signed { 's' } else { 'u' }",
    src_type,
    dst_type,
    src
)]
pub struct IntToFloatInstr {
    signed: bool,
    src_type: IntType,
    dst_type: FloatType,
    src: Value,
}

impl IntToFloatInstr {
    /// Creates a new instruction that converts from an integer to a floating point number.
    pub fn new(
        signed: bool,
        src_type: IntType,
        dst_type: FloatType,
        src: Value,
    ) -> Self {
        Self {
            signed,
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source type of the truncate instruction.
    pub fn src_type(&self) -> IntType {
        self.src_type
    }

    /// Returns the destination type of the truncate instruction.
    pub fn dst_type(&self) -> FloatType {
        self.dst_type
    }

    /// Returns the source of the instruction that is to be extended.
    pub fn src(&self) -> Value {
        self.src
    }

    /// Returns `true` if the source is treated as a signed integer.
    ///
    /// - `true`: `sign-extension`
    /// - `false`: `zero-extension`
    pub fn is_signed(&self) -> bool {
        self.signed
    }

    /// Replaces all values in the instruction using the replacer.
    ///
    /// Returns `true` if a value has been replaced in the instruction.
    ///
    /// # Note
    ///
    /// By contract the replacer returns `true` if replacement happened.
    pub fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.src)
    }
}
