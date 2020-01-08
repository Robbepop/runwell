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

/// A typed identifier used to index into a table of entities.
pub trait Identifier: Copy {
    /// Returns the underlying `usize` of the identifier.
    fn get(self) -> usize;
}

/// An index into the function signature table of a Wasm module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionSigId(pub(super) usize);

impl Identifier for FunctionSigId {
    fn get(self) -> usize {
        self.0
    }
}

/// An index into the internal global variable table of a Wasm module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GlobalVariableId(pub(super) usize);

impl Identifier for GlobalVariableId {
    fn get(self) -> usize {
        self.0
    }
}

/// An index into the function table of a Wasm module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionId(pub(super) usize);

impl Identifier for FunctionId {
    fn get(self) -> usize {
        self.0
    }
}

/// An index into the linear memory table of a Wasm module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LinearMemoryId(pub(super) usize);

impl Identifier for LinearMemoryId {
    fn get(self) -> usize {
        self.0
    }
}

impl Default for LinearMemoryId {
    /// Returns the `0` linear memory ID.
    ///
    /// Operations that do not include a linear memory ID implicitely refer
    /// to the linear memory identified by the `0` ID.
    fn default() -> Self {
        Self(0)
    }
}

/// An index into the table section of a Wasm module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TableId(pub(super) usize);

impl Identifier for TableId {
    fn get(self) -> usize {
        self.0
    }
}

impl Default for TableId {
    /// Returns the `0` table ID.
    ///
    /// Operations that do not include a table ID implicitely refer
    /// to the table identified by the `0` ID.
    fn default() -> Self {
        Self(0)
    }
}
