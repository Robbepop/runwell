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

use crate::Index32;

define_id_type! {
    /// An index into the function signature table of a Wasm module.
    pub struct FunctionTypeId;
}
define_id_type! {
    /// An index into the internal global variable table of a Wasm module.
    pub struct GlobalVariableId;
}
define_id_type! {
    /// An index into the function table of a Wasm module.
    pub struct FunctionId;
}
define_id_type! {
    /// An index into the linear memory table of a Wasm module.
    pub struct LinearMemoryId;
}

impl Default for LinearMemoryId {
    /// Returns the `0` linear memory ID.
    ///
    /// Operations that do not include a linear memory ID implicitely refer
    /// to the linear memory identified by the `0` ID.
    fn default() -> Self {
        Self::from_u32(0)
    }
}

define_id_type! {
    /// An index into the table section of a Wasm module.
    pub struct TableId;
}

impl Default for TableId {
    /// Returns the `0` table ID.
    ///
    /// Operations that do not include a table ID implicitely refer
    /// to the table identified by the `0` ID.
    fn default() -> Self {
        Self::from_u32(0)
    }
}
