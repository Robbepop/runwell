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

use crate::ir::{IntType, Value};
use derive_more::Display;

/// Truncates the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be greater than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "truncate {} -> {}, src {}", src_type, dst_type, src)]
pub struct TruncateInstr {
    src_type: IntType,
    dst_type: IntType,
    src: Value,
}

impl TruncateInstr {
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
    pub fn src_type(&self) -> &IntType {
        &self.src_type
    }

    /// Returns the destination type of the truncate instruction.
    pub fn dst_type(&self) -> &IntType {
        &self.src_type
    }
}

/// Zero-extends the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be less than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "extend.zero {} -> {}, src {}", src_type, dst_type, src)]
pub struct ZeroExtendInstr {
    src_type: IntType,
    dst_type: IntType,
    src: Value,
}

impl ZeroExtendInstr {
    /// Creates a new zero-extend instruction extending src from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be less than the bit width of the destination type.
    pub fn new(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        assert!(src_type.bit_width() > dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source type of the truncate instruction.
    pub fn src_type(&self) -> &IntType {
        &self.src_type
    }

    /// Returns the destination type of the truncate instruction.
    pub fn dst_type(&self) -> &IntType {
        &self.src_type
    }
}

/// Sign-extends the integer value from source type to destination type.
///
/// # Note
///
/// The bit width of the source type must be less than the bit width of the destination type.
#[derive(Debug, Display, PartialEq, Eq)]
#[display(fmt = "extend.sign {} -> {}, src {}", src_type, dst_type, src)]
pub struct SignExtendInstr {
    src_type: IntType,
    dst_type: IntType,
    src: Value,
}

impl SignExtendInstr {
    /// Creates a new sign-extend instruction extending src from source type to destination type.
    ///
    /// # Note
    ///
    /// The bit width of the source type must be less than the bit width of the destination type.
    pub fn new(src_type: IntType, dst_type: IntType, src: Value) -> Self {
        assert!(src_type.bit_width() > dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source type of the truncate instruction.
    pub fn src_type(&self) -> &IntType {
        &self.src_type
    }

    /// Returns the destination type of the truncate instruction.
    pub fn dst_type(&self) -> &IntType {
        &self.src_type
    }
}
