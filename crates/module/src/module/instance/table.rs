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

use crate::{primitive::InitExpr, Module, ModuleResources};
use entity::{ComponentMap, RawIdx};
use ir::primitive::{Func, Mem, Table};

/// The contents of an instantiated table.
#[derive(Debug, Default)]
pub struct TableContents {
    elements: Vec<Func>,
}

impl TableContents {
    /// Initializes parts of the table contents.
    pub fn initialize(&mut self, offset: u32, funcs: &[Func]) {
        let null = Func::from_raw(RawIdx::from_u32(0));
        let offset = offset as usize;
        self.elements.resize(offset + funcs.len(), null);
        self.elements[offset..(offset + funcs.len())].copy_from_slice(funcs);
    }
}
