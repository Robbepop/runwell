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

use crate::ir::{FloatType, Value};
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
