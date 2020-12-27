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

use crate::ir::{Type, Value};
use derive_more::Display;

/// Reinterprets the bytes of the source from source type to destination type.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(fmt = "reinterpret {} -> {}, source {}", src_type, dst_type, src)]
pub struct ReinterpretInstr {
    src_type: Type,
    dst_type: Type,
    src: Value,
}

impl ReinterpretInstr {
    /// Creates a new reinterpret instruction.
    ///
    /// Reinterprets the bytes of the source from source type to destination type.
    ///
    /// # Note
    ///
    /// Both, source type and destination type must have equal bit widths.
    /// Source type and destination type must be different types.
    pub fn new(src_type: Type, dst_type: Type, src: Value) -> Self {
        assert_ne!(src_type, dst_type);
        assert_eq!(src_type.bit_width(), dst_type.bit_width());
        Self {
            src_type,
            dst_type,
            src,
        }
    }

    /// Returns the source type of the reinterpret instruction.
    pub fn src_type(&self) -> &Type {
        &self.src_type
    }

    /// Returns the destination type of the reinterpret instruction.
    pub fn dst_type(&self) -> &Type {
        &self.src_type
    }
}
