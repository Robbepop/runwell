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
pub struct Export {
    /// The export field name.
    field: String,
    /// The export kind.
    kind: ExportKind,
}

impl Export {
    /// Returns the export kind.
    ///
    /// # Note
    ///
    /// Use this to extract further information about the exported entity.
    pub fn kind(&self) -> &ExportKind {
        &self.kind
    }
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

impl<'a> From<wasmparser::Export<'a>> for Export {
    fn from(wasm_export: wasmparser::Export<'a>) -> Self {
        let id = wasm_export.index;
        Self {
            field: wasm_export.field.to_string(),
            kind: match wasm_export.kind {
                ExternalKind::Function => ExportKind::Function(FunctionId::from_u32(id)),
                ExternalKind::Global => {
                    ExportKind::Global(GlobalVariableId::from_u32(id))
                }
                ExternalKind::Memory => ExportKind::Memory(LinearMemoryId::from_u32(id)),
                ExternalKind::Table => ExportKind::Table(TableId::from_u32(id)),
                ExternalKind::Event => {
                    unimplemented!("event exports are not supported by the Runwell JIT")
                }
                ExternalKind::Module => {
                    unimplemented!("module exports are not supported by the Runwell JIT")
                }
                ExternalKind::Instance => {
                    unimplemented!("instance exports are not supported by the Runwell JIT")
                }
                ExternalKind::Type => {
                    unimplemented!("type exports are not supported by the Runwell JIT")
                }
            },
        }
    }
}

/// An element of the element section of a Wasm module.
#[derive(Debug)]
pub struct Element {
    /// The referred to table index.
    table_id: TableId,
    /// The offset within the table for the initialized elements.
    offset: Initializer,
    /// The function signatures for the initialized table elements.
    items: Box<[FunctionId]>,
}

impl<'a> core::convert::TryFrom<wasmparser::Element<'a>> for Element {
    type Error = ParseError;

    fn try_from(element: wasmparser::Element<'a>) -> Result<Self, Self::Error> {
        use wasmparser::ElementKind;
        match element.kind {
            ElementKind::Passive => {
                Err(ParseError::UnsupportedPassiveElement)
            }
            ElementKind::Declared => {
                Err(ParseError::UnsupportedDeclaredElement)
            }
            ElementKind::Active {
                table_index,
                init_expr,
            } => {
                let table_id = TableId::from_u32(table_index);
                let offset = Initializer::try_from(init_expr)?;
                let items = {
                    let mut reader = element.items.get_items_reader()?;
                    let mut items = Vec::new();
                    while let Ok(kind) = reader.read() {
                        match kind {
                            wasmparser::ElementItem::Null(_type) => {
                                return Err(ParseError::UnsupportedElementKind)
                            }
                            wasmparser::ElementItem::Func(id) => {
                                items.push(FunctionId::from_u32(id))
                            }
                        }
                    }
                    items.into_boxed_slice()
                };
                // TODO: Replace above code with iterator based version after
                //       https://github.com/bytecodealliance/wasmparser/issues/167
                //       has been implemented, merged and released.
                Ok(Element {
                    table_id,
                    offset,
                    items,
                })
            }
        }
    }
}

impl Element {
    /// Returns the table index.
    pub fn table_id(&self) -> TableId {
        self.table_id
    }

    /// Returns the offset initializer expression.
    pub fn offset(&self) -> &Initializer {
        &self.offset
    }

    /// Returns the functions with which the elements shall be initialized.
    pub fn items<'a>(&'a self, module: &'a Module) -> ElementItemsIter<'a> {
        ElementItemsIter::new(self, module)
    }
}

/// An iterator over the element items of a Wasm module element.
pub struct ElementItemsIter<'a> {
    /// The associated Wasm module.
    module: &'a Module,
    /// The element items.
    items: core::slice::Iter<'a, FunctionId>,
}

impl<'a> ElementItemsIter<'a> {
    /// Creates a new element items iterator.
    fn new(element: &'a Element, module: &'a Module) -> Self {
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
