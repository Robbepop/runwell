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

use crate::{
    primitive::{FloatType, IntType, Value},
    VisitValues,
    VisitValuesMut,
};
use derive_more::Display;

/// Truncates the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be greater than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "itruncate {} -> {}, src {}", src_type, dst_type, src)]
pub struct TruncateIntInstr {
    src_type: IntType,
    dst_type: IntType,
    src: Value,
}

impl TruncateIntInstr {
    /// Creates a new truncation instruction truncating `src` from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be greater than the bit width of the destination type.
    pub fn new(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        assert!(src_type.bit_width() >= dst_type.bit_width());
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
}

impl VisitValues for TruncateIntInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.src);
    }
}

impl VisitValuesMut for TruncateIntInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.src);
    }
}

/// Extends the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be less than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(
    fmt = "{}extend {} -> {} {}",
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
    /// Creates a new extension instruction extending `src` from source type to destination type.
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
        assert!(src_type.bit_width() <= dst_type.bit_width());
        Self {
            signed,
            src_type,
            dst_type,
            src,
        }
    }

    /// Creates a new zero-extend instruction extending `src` from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be less than the bit width of the destination type.
    pub fn zext(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        Self::new(false, src_type, dst_type, src)
    }

    /// Creates a new sign-extend instruction extending `src` from source type to destination type.
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
}

impl VisitValues for ExtendIntInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.src);
    }
}

impl VisitValuesMut for ExtendIntInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.src);
    }
}

/// Instruction to convert an integer into a floating point number.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(
    fmt = "{}convert {} -> {} {}",
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
}

impl VisitValues for IntToFloatInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.src);
    }
}

impl VisitValuesMut for IntToFloatInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.src);
    }
}
