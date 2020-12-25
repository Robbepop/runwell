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

use crate::ir::{FloatType, IntType, Value};
use derive_more::Display;

/// Demotes the source float value from source float type to destination float type.
///
/// # Note
///
/// The bit width of destination float type must be smaller than the bit width of the
/// source float type.
#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "demote {} -> {}, source {}", src_type, dst_type, src)]
pub struct FdemoteInstr {
    src_type: FloatType,
    dst_type: FloatType,
    src: Value,
}

impl FdemoteInstr {
    /// Creates a new float demote instruction.
    pub fn new(src_type: FloatType, dst_type: FloatType, src: Value) -> Self {
        Self {
            src_type,
            dst_type,
            src,
        }
    }
}

/// Demotes the source float value from source float type to destination float type.
///
/// # Note
///
/// The bit width of destination float type must be bigger than the bit width of the
/// source float type.
#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "promote {} -> {}, source {}", src_type, dst_type, src)]
pub struct FpromoteInstr {
    src_type: FloatType,
    dst_type: FloatType,
    src: Value,
}

impl FpromoteInstr {
    /// Creates a new float promote instruction.
    pub fn new(src_type: FloatType, dst_type: FloatType, src: Value) -> Self {
        Self {
            src_type,
            dst_type,
            src,
        }
    }
}

/// Instruction to convert a floating point number into an unsigned integer.
///
/// # Note
///
/// Truncates the given floating point number (towards zero) to cast into the integer.
/// Interprets the integer as **unsigned** integer.
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

#[derive(Debug, Display, PartialEq, Eq)]
#[display(
    fmt = "convert {} -> {} unsigned, src {}, saturating {}",
    src_type,
    dst_type,
    src,
    saturating
)]
pub struct FtoUintInstr {
    src_type: FloatType,
    dst_type: IntType,
    src: Value,
    saturating: bool,
}

impl FtoUintInstr {
    /// Creates a new instruction converts from float to unsigned integer type.
    ///
    /// # Note
    ///
    /// The source type must have a bit width that is greater than or equal to the bit width
    /// of the destination type.
    pub fn new(
        src_type: FloatType,
        dst_type: IntType,
        src: Value,
        saturating: bool,
    ) -> Self {
        assert!(src_type.bit_width() >= dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
            saturating,
        }
    }
}

/// Instruction to convert a floating point number into a signed integer.
///
/// # Note
///
/// Truncates the given floating point number (towards zero) to cast into the integer.
/// Interprets the integer as **signed** integer.
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
#[derive(Debug, Display, PartialEq, Eq)]
#[display(
    fmt = "convert {} -> {} signed, src {}, saturating {}",
    src_type,
    dst_type,
    src,
    saturating
)]
pub struct FtoSintInstr {
    src_type: FloatType,
    dst_type: IntType,
    src: Value,
    saturating: bool,
}

impl FtoSintInstr {
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
        src: Value,
        saturating: bool,
    ) -> Self {
        assert!(src_type.bit_width() >= dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
            saturating,
        }
    }
}
