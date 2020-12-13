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

use crate::parse::{FunctionId, GlobalInitExpr, ComilerError, TableId};
use std::{collections::HashMap, convert::TryFrom};
use wasmparser::{ElementItems, ElementItemsReader, ResizableLimits};

/// A Wasm table declaration.
#[derive(Debug)]
pub struct TableDecl {
    limits: ResizableLimits,
    items: TableItems,
}

impl TableDecl {
    /// Returns a mutable reference to the items with which the table is initialized.
    pub fn items_mut(&mut self) -> &mut TableItems {
        &mut self.items
    }
}

impl TryFrom<wasmparser::TableType> for TableDecl {
    type Error = ComilerError;

    fn try_from(
        table_type: wasmparser::TableType,
    ) -> Result<Self, Self::Error> {
        match table_type.element_type {
            wasmparser::Type::FuncRef => (),
            _unsupported => return Err(ComilerError::UnsupportedElementKind),
        }
        Ok(Self {
            limits: table_type.limits,
            items: TableItems::default(),
        })
    }
}

/// A parsed and validated element from the element section of a Wasm module.
pub struct Element<'a> {
    /// The referred to table index.
    pub table_id: TableId,
    /// The offset within the table for the initialized elements.
    pub offset: GlobalInitExpr,
    /// The function signatures for the initialized table elements.
    items: ElementItems<'a>,
}

/// An iterator yielding all the element items within an element segment.
pub struct ElementItemsIter<'a> {
    /// The amount of remaining items that this iterator will yield.
    remaining: usize,
    /// The underlying iterator from the `wasmparser` crate.
    items: ElementItemsReader<'a>,
}

impl<'a> From<ElementItemsReader<'a>> for ElementItemsIter<'a> {
    fn from(items: ElementItemsReader<'a>) -> Self {
        Self {
            remaining: items.get_count() as usize,
            items,
        }
    }
}

impl<'a> Iterator for ElementItemsIter<'a> {
    type Item = Result<FunctionId, ComilerError>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None
        }
        match self.items.read() {
            Ok(element_item) => {
                match element_item {
                    wasmparser::ElementItem::Func(func_id) => {
                        let func_id = FunctionId::from_u32(func_id);
                        self.remaining -= 1;
                        Some(Ok(func_id))
                    }
                    wasmparser::ElementItem::Null(_) => {
                        Some(Err(ComilerError::InvalidElementItem))
                    }
                }
            }
            Err(_error) => {
                // TODO: Implement better error reporting here.
                Some(Err(ComilerError::InvalidElementItem))
            }
        }
    }
}

impl<'a> core::iter::ExactSizeIterator for ElementItemsIter<'a> {}
impl<'a> core::iter::FusedIterator for ElementItemsIter<'a> {}

impl<'a> core::fmt::Debug for Element<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Element")
            .field("table_id", &self.table_id)
            .field("offset", &self.offset)
            .field(
                "items",
                &self
                    .items()
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|_| core::fmt::Error)?,
            )
            .finish()
    }
}

impl<'a> Element<'a> {
    /// Returns an iterator yielding all the elements of this element segment.
    pub fn items(&self) -> ElementItemsIter<'a> {
        let reader = self
            .items
            .get_items_reader()
            .expect("encountered unexpected invalid items reader");
        ElementItemsIter::from(reader)
    }
}

impl<'a> core::convert::TryFrom<wasmparser::Element<'a>> for Element<'a> {
    type Error = ComilerError;

    fn try_from(element: wasmparser::Element<'a>) -> Result<Self, Self::Error> {
        use wasmparser::ElementKind;
        match element.kind {
            ElementKind::Passive => Err(ComilerError::UnsupportedPassiveElement),
            ElementKind::Declared => {
                Err(ComilerError::UnsupportedDeclaredElement)
            }
            ElementKind::Active {
                table_index,
                init_expr,
            } => {
                let table_id = TableId::from_u32(table_index);
                let offset = GlobalInitExpr::try_from(init_expr)?;
                let items = element.items;
                // With this upfront check we can drop the same check in [`Element::items`] and
                // instead directly panic if this condition is violated there which simplifies
                // the overall API.
                let _ = items
                    .get_items_reader()
                    .map_err(|_| ComilerError::InvalidElementItem)?;
                Ok(Self {
                    table_id,
                    offset,
                    items,
                })
            }
        }
    }
}

/// The elements with which a Wasm table has been initialized.
///
/// This is a mapping from an index to a function reference.
/// Value types besides function references are not yet supported.
#[derive(Debug, Default)]
pub struct TableItems {
    items: HashMap<usize, FunctionId>,
}

impl TableItems {
    /// Pushes the given element items to the table elements.
    ///
    /// This might overwrite previous element items with the same indices.
    ///
    /// # Errors
    ///
    /// If there are invalid table element items.
    pub fn set_items<I>(
        &mut self,
        offset: usize,
        items: I,
    ) -> Result<(), ComilerError>
    where
        I: IntoIterator<Item = FunctionId>,
    {
        for (index, item) in items.into_iter().enumerate() {
            self.items.insert(offset + index, item);
        }
        Ok(())
    }

    /// Returns the function reference at the given index if any.
    pub fn get(&self, index: usize) -> Option<FunctionId> {
        self.items.get(&index).copied()
    }
}
