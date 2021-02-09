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
    ReplaceValue,
};
use derive_more::Display;

/// Demotes the source float value from source float type to destination float type.
///
/// # Note
///
/// The bit width of destination float type must be smaller than the bit width of the
/// source float type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "fdemote {} -> {} {}", src_type, dst_type, src)]
pub struct DemoteFloatInstr {
    src_type: FloatType,
    dst_type: FloatType,
    src: Value,
}

impl DemoteFloatInstr {
    /// Creates a new float demote instruction.
    ///
    /// # Panics
    ///
    /// If the destination floating point number type has a bit width greater
    /// than the source floating point number type.
    pub fn new(src_type: FloatType, dst_type: FloatType, src: Value) -> Self {
        assert!(src_type.bit_width() >= dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source floating point number type before demotion.
    pub fn src_type(&self) -> FloatType {
        self.src_type
    }

    /// Returns the target floating point number type after demotion.
    pub fn dst_type(&self) -> FloatType {
        self.dst_type
    }

    /// Returns the source floating point value of the demotion.
    pub fn src(&self) -> Value {
        self.src
    }
}

impl ReplaceValue for DemoteFloatInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.src)
    }
}

/// Demotes the source float value from source float type to destination float type.
///
/// # Note
///
/// The bit width of destination float type must be bigger than the bit width of the
/// source float type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "fpromote {} -> {} {}", src_type, dst_type, src)]
pub struct PromoteFloatInstr {
    src_type: FloatType,
    dst_type: FloatType,
    src: Value,
}

impl PromoteFloatInstr {
    /// Creates a new float promote instruction.
    ///
    /// # Panics
    ///
    /// If the destination floating point number type has a bit width smaller
    /// than the source floating point number type.
    pub fn new(src_type: FloatType, dst_type: FloatType, src: Value) -> Self {
        assert!(src_type.bit_width() <= dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source floating point number type before promotion.
    pub fn src_type(&self) -> FloatType {
        self.src_type
    }

    /// Returns the target floating point number type after promotion.
    pub fn dst_type(&self) -> FloatType {
        self.dst_type
    }

    /// Returns the source floating point value of the promotion.
    pub fn src(&self) -> Value {
        self.src
    }
}

impl ReplaceValue for PromoteFloatInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.src)
    }
}

/// Instruction to convert a floating point number into an integer.
///
/// # Note
///
/// Truncates the given floating point number (towards zero) to cast into the integer.
/// Interprets the resulting integer as either a **signed** or an **unsigned** integer
/// depending on the `dst_signed` field.
///
/// Truncation from floating point to integer where IEEE 754-2008 would specify an invalid
/// operator exception (e.g. when the floating point value is NaN or outside the range which
/// rounds to an integer in range) is handled as follows:
///
/// If `saturating` is `false`:
///    - A trap is produced.
/// If `saturating` is `true`:
///    - No trap is produced.
///    - If the floating-point value is positive, the maximum integer value is returned.
///    - If the floating-point value is negative, the minimum integer value is returned.
///    - If the floating-point value is NaN, zero is returned.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(
    fmt = "fconvert_{} {} -> {}, src {}, saturating {}",
    "if self.dst_signed { 's' } else { 'u' }",
    src_type,
    dst_type,
    src,
    saturating
)]
pub struct FloatToIntInstr {
    src_type: FloatType,
    dst_type: IntType,
    dst_signed: bool,
    src: Value,
    saturating: bool,
}

impl FloatToIntInstr {
    /// Creates a new instruction converts from float to signed integer type.
    ///
    /// # Note
    ///
    /// The source type must have a bit width that is greater than or equal to the bit width
    /// of the destination type.
    /// The `signed` flag tells if the conversion from float to integer shall treat the
    /// resulting integer as signed or unsigned integer type.
    pub fn new(
        src_type: FloatType,
        dst_type: IntType,
        dst_signed: bool,
        src: Value,
        saturating: bool,
    ) -> Self {
        Self {
            src_type,
            dst_type,
            dst_signed,
            src,
            saturating,
        }
    }

    /// Returns the source floating point number type before conversion.
    pub fn src_type(&self) -> FloatType {
        self.src_type
    }

    /// Returns the destination integer type after conversion.
    pub fn dst_type(&self) -> IntType {
        self.dst_type
    }

    /// Returns the source floating point value of the conversion.
    pub fn src(&self) -> Value {
        self.src
    }

    /// Returns `true` if the resulting integer is interpreted as signed integer.
    pub fn is_signed(&self) -> bool {
        self.dst_signed
    }

    /// Returns `true` if the conversion is saturating.
    pub fn is_saturating(&self) -> bool {
        self.saturating
    }
}

impl ReplaceValue for FloatToIntInstr {
    fn replace_value<F>(&mut self, mut replace: F) -> bool
    where
        F: FnMut(&mut Value) -> bool,
    {
        replace(&mut self.src)
    }
}
