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

use super::{builder::WasmSectionEntry, BuildError};
use crate::parse::{FunctionId, GlobalInitExpr, ParseError, TableId};
use std::{convert::TryFrom, collections::{hash_map::Entry, HashMap}};
use wasmparser::{ElementItems, ElementItemsReader, ResizableLimits};

/// A Wasm table declaration.
#[derive(Debug)]
pub struct TableDecl {
    limits: ResizableLimits,
}

impl TryFrom<wasmparser::TableType> for TableDecl {
    type Error = ParseError;

    fn try_from(table_type: wasmparser::TableType) -> Result<Self, Self::Error> {
        match table_type.element_type {
            wasmparser::Type::FuncRef => (),
            _unsupported => {
                return Err(ParseError::UnsupportedElementKind)
            }
        }
        Ok(Self { limits: table_type.limits })
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
    type Item = Result<FunctionId, ParseError>;

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
                        return Some(Ok(func_id))
                    }
                    wasmparser::ElementItem::Null(_) => {
                        return Some(Err(ParseError::InvalidElementItem))
                    }
                }
            }
            Err(_error) => {
                // TODO: Implement better error reporting here.
                return Some(Err(ParseError::InvalidElementItem))
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
    type Error = ParseError;

    fn try_from(element: wasmparser::Element<'a>) -> Result<Self, Self::Error> {
        use wasmparser::ElementKind;
        match element.kind {
            ElementKind::Passive => Err(ParseError::UnsupportedPassiveElement),
            ElementKind::Declared => {
                Err(ParseError::UnsupportedDeclaredElement)
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
                    .map_err(|_| ParseError::InvalidElementItem)?;
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
pub struct TableElements {
    items: HashMap<usize, FunctionId>,
}

impl TableElements {
    pub fn set_items<I>(
        &mut self,
        offset: usize,
        items: I,
    ) -> Result<(), ParseError>
    where
        I: IntoIterator<Item = FunctionId>,
    {
        for (index, item) in items.into_iter().enumerate() {
            self.items.insert(offset + index, item);
        }
        Ok(())
    }

    /// Pushes another element to the table at the given index.
    ///
    /// # Errors
    ///
    /// If the table already stores an element for the same index.
    pub fn set_func_ref(
        &mut self,
        index: usize,
        func_ref: FunctionId,
    ) -> Result<(), ParseError> {
        match self.items.entry(index) {
            Entry::Occupied(_occupied) => {
                return Err(ParseError::InvalidElementItem)
            }
            Entry::Vacant(vacant) => {
                vacant.insert(func_ref);
                Ok(())
            }
        }
    }

    /// Returns the function reference at the given index if any.
    pub fn func_ref(&self, index: usize) -> Option<FunctionId> {
        self.items.get(&index).copied()
    }
}

/// The elements of all declared tables.
#[derive(Debug, Default)]
pub struct Tables {
    /// One entry per declared table.
    ///
    /// Stores all the elements of the table.
    tables: Vec<TableElements>,
}

impl Tables {
    /// Sets the number of table definitions to the given value.
    ///
    /// # Errors
    ///
    /// If a reservation for a total number of tables has already happened.
    pub fn reserve_total_tables(
        &mut self,
        count_total: usize,
    ) -> Result<(), ParseError> {
        if !self.tables.is_empty() {
            return Err(ParseError::Build(BuildError::DuplicateReservation {
                entry: WasmSectionEntry::Table,
                reserved: count_total,
                previous: self.tables.len(),
            }))
        }
        self.tables.resize_with(count_total, Default::default);
        Ok(())
    }

    /// Ensures that the given table ID is valid.
    ///
    /// # Panics
    ///
    /// If the given table ID is out of bounds.
    fn ensure_valid_table_id(&self, id: TableId) -> usize {
        let id = id.into_u32() as usize;
        let len_tables = self.tables.len();
        assert!(
            id < len_tables,
            "encountered unexpected out of bounds table ID: {}, len tables: {}",
            id,
            len_tables
        );
        id
    }

    /// Returns the elements of the table given the table ID.
    ///
    /// # Panics
    ///
    /// If the table ID is invalid.
    pub fn table(&self, id: TableId) -> &TableElements {
        &self.tables[self.ensure_valid_table_id(id)]
    }

    /// Returns a mutable reference to the elements of the table given the table ID.
    ///
    /// # Panics
    ///
    /// If the table ID is invalid.
    pub fn table_mut(&mut self, id: TableId) -> &mut TableElements {
        let id = self.ensure_valid_table_id(id);
        &mut self.tables[id]
    }
}
