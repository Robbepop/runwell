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

use crate::parse::{
    Function,
    FunctionId,
    GlobalVariableId,
    Initializer,
    LinearMemoryId,
    Module,
    ParseError,
    TableId,
};
use wasmparser::ExternalKind;

/// An export definition of a Wasm module.
#[derive(Debug)]
pub struct Export<'a> {
    /// The export field name.
    field: &'a str,
    /// The export kind.
    kind: ExportKind,
}

/// An export kind of an export definition.
#[derive(Debug)]
pub enum ExportKind {
    /// An exported function.
    Function(FunctionId),
    /// An exported global variable.
    Global(GlobalVariableId),
    /// An exported linear memory.
    Memory(LinearMemoryId),
    /// An exported table.
    Table(TableId),
}

impl<'a> From<wasmparser::Export<'a>> for Export<'a> {
    fn from(wasm_export: wasmparser::Export<'a>) -> Self {
        let id = wasm_export.index as usize;
        Self {
            field: wasm_export.field,
            kind: match wasm_export.kind {
                ExternalKind::Function => ExportKind::Function(FunctionId(id)),
                ExternalKind::Global => {
                    ExportKind::Global(GlobalVariableId(id))
                }
                ExternalKind::Memory => ExportKind::Memory(LinearMemoryId(id)),
                ExternalKind::Table => ExportKind::Table(TableId(id)),
            },
        }
    }
}

/// An element of the element section of a Wasm module.
#[derive(Debug)]
pub struct Element<'a> {
    /// The referred to table index.
    table_id: TableId,
    /// The offset within the table for the initialized elements.
    offset: Initializer<'a>,
    /// The function signatures for the initialized table elements.
    items: Box<[FunctionId]>,
}

impl<'a> core::convert::TryFrom<wasmparser::Element<'a>> for Element<'a> {
    type Error = ParseError;

    fn try_from(element: wasmparser::Element<'a>) -> Result<Self, Self::Error> {
        use wasmparser::ElementKind;
        match element.kind {
            ElementKind::Passive { .. } => {
                Err(ParseError::UnsupportedPassiveElement)
            }
            ElementKind::Active {
                table_index,
                init_expr,
                items,
            } => {
                let table_id = TableId(table_index as usize);
                let offset = Initializer::try_from(init_expr)?;
                let items = {
                    let mut reader = items.get_items_reader()?;
                    let mut items = Vec::new();
                    while let Ok(id) = reader.read() {
                        items.push(FunctionId(id as usize))
                    }
                    items.into_boxed_slice()
                };
                // TODO: Replace above code with below code after
                //       https://github.com/bytecodealliance/wasmparser/issues/167
                //       has been implemented, merged and released.
                //
                // let items = items
                //     .get_items_reader()
                //     .into_iter()
                //     .map(|id| FunctionId(id as usize))
                //     .collect::<Result<Vec<_>, _>>()?
                //     .into_boxed_slice();
                Ok(Element {
                    table_id,
                    offset,
                    items,
                })
            }
        }
    }
}

impl<'a> Element<'a> {
    /// Returns the table index.
    pub fn table_id(&self) -> TableId {
        self.table_id
    }

    /// Returns the offset initializer expression.
    pub fn offset(&'a self) -> &'a Initializer<'a> {
        &self.offset
    }

    /// Returns the functions with which the elements shall be initialized.
    pub fn items(&'a self, module: &'a Module<'a>) -> ElementItemsIter<'a> {
        ElementItemsIter::new(self, module)
    }
}

/// An iterator over the element items of a Wasm module element.
pub struct ElementItemsIter<'a> {
    /// The associated Wasm module.
    module: &'a Module<'a>,
    /// The element items.
    items: core::slice::Iter<'a, FunctionId>,
}

impl<'a> ElementItemsIter<'a> {
    /// Creates a new element items iterator.
    fn new(element: &'a Element<'a>, module: &'a Module<'a>) -> Self {
        Self {
            module,
            items: element.items.iter(),
        }
    }
}

impl<'a> Iterator for ElementItemsIter<'a> {
    type Item = Function<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.items.next().map(|&fn_id| self.module.get_fn(fn_id))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.items.size_hint()
    }
}

impl<'a> DoubleEndedIterator for ElementItemsIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.items
            .next_back()
            .map(|&fn_id| self.module.get_fn(fn_id))
    }
}

impl<'a> core::iter::ExactSizeIterator for ElementItemsIter<'a> {}

impl<'a> core::iter::FusedIterator for ElementItemsIter<'a> {}
