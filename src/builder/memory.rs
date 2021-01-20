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

use crate::parse::{self, InitializerExpr, ParseError};

/// A parsed and validated Wasm linear memory with its data items.
#[derive(Debug)]
pub struct LinearMemory {
    pub decl: parse::LinearMemory,
    pub data: LinearMemoryData,
}

impl From<parse::LinearMemory> for LinearMemory {
    fn from(memory: parse::LinearMemory) -> Self {
        Self {
            decl: memory,
            data: LinearMemoryData::default(),
        }
    }
}

/// The contents of a Wasm linear memory.
#[derive(Debug, Default)]
pub struct LinearMemoryData {
    /// Data items.
    ///
    /// These are used to initialize the linear memory upon module instantiation.
    items: Vec<Data>,
}

impl LinearMemoryData {
    /// Initializes the region starting at `offset` with the given byte sequence.
    ///
    /// Consecutive calls to `init_region` might overwrite past initializations.
    pub fn init_region(
        &mut self,
        offset: InitializerExpr,
        bytes: &[u8],
    ) -> Result<(), ParseError> {
        self.items.push(Data {
            offset,
            bytes: bytes.to_vec(),
        });
        Ok(())
    }
}

/// A data segment item with a non constant initializer expression.
#[derive(Debug)]
pub struct Data {
    offset: InitializerExpr,
    bytes: Vec<u8>,
}
