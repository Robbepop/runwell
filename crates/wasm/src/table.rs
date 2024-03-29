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

use super::{Error, InitExpr};
use core::convert::TryFrom;
use derive_more::Display;
use entity::RawIdx;
use ir::primitive::{Func, Table};

/// An error that might occur while parsing or validating tables or table elements.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum TableError {
    #[display(fmt = "encountered invalid table element type: {:?}", _0)]
    InvalidTableElementType(wasmparser::Type),
    #[display(
        fmt = "encountered unsupported initializer expression element item"
    )]
    UnsupportedExprElementItem,
    #[display(fmt = "encountered unsupported passive table element")]
    UnsupportedPassiveElement,
    #[display(fmt = "encountered unsupported declared table element")]
    UnsupportedDeclaredElement,
}

impl std::error::Error for TableError {}

/// A Wasm table declaration.
#[derive(Debug)]
pub struct TableDecl {
    inner: module::primitive::TableDecl,
}

impl TableDecl {
    /// Returns the inner Runwell table declaration.
    pub fn into_inner(self) -> module::primitive::TableDecl {
        self.inner
    }
}

impl TryFrom<wasmparser::TableType> for TableDecl {
    type Error = Error;

    fn try_from(
        table_type: wasmparser::TableType,
    ) -> Result<Self, Self::Error> {
        match table_type.element_type {
            wasmparser::Type::FuncRef => (),
            invalid => {
                return Err(TableError::InvalidTableElementType(invalid))
                    .map_err(Into::into)
            }
        }
        let initial_size = table_type.initial;
        let maximum_size = table_type.maximum;
        Ok(Self {
            inner: module::primitive::TableDecl::new(
                initial_size,
                maximum_size,
            ),
        })
    }
}

/// A parsed and validated element from the element section of a Wasm module.
pub struct Element<'a> {
    /// The table for which the element serves as initializer.
    table: Table,
    /// The offset within the table for the initialized elements.
    offset: InitExpr,
    /// The function references for the initialized table.
    func_refs: wasmparser::ElementItems<'a>,
}

impl<'a> Element<'a> {
    /// Returns the table for which the element serves as initializer.
    pub fn table(&self) -> Table {
        self.table
    }

    /// Returns the offset initializer expression for the element.
    pub fn offset(self) -> module::primitive::InitExpr {
        self.offset.into_inner()
    }

    /// Returns an iterator yielding all the elements of this element segment.
    pub fn items(&self) -> ElementItemsIter<'a> {
        let reader = self.func_refs.get_items_reader().expect(
            "this has already been asserted at the TryFrom impl of Element and therefore must not fail",
        );
        ElementItemsIter::from(reader)
    }
}

impl<'a> TryFrom<wasmparser::Element<'a>> for Element<'a> {
    type Error = Error;

    fn try_from(element: wasmparser::Element<'a>) -> Result<Self, Self::Error> {
        use wasmparser::ElementKind;
        match element.kind {
            ElementKind::Passive => {
                Err(TableError::UnsupportedPassiveElement).map_err(Into::into)
            }
            ElementKind::Declared => {
                Err(TableError::UnsupportedDeclaredElement).map_err(Into::into)
            }
            ElementKind::Active {
                table_index,
                init_expr,
            } => {
                let table = Table::from_raw(RawIdx::from_u32(table_index));
                let offset = InitExpr::try_from(init_expr)?;
                let func_refs = element.items;
                // With this upfront check we can drop the same check in [`Element::items`] and
                // instead directly panic if this condition is violated there which simplifies
                // the overall API.
                let _ = func_refs.get_items_reader()?;
                Ok(Self {
                    table,
                    offset,
                    func_refs,
                })
            }
        }
    }
}

impl<'a> core::fmt::Debug for Element<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Element")
            .field("table", &self.table)
            .field("offset", &self.offset)
            .field(
                "func_refs",
                &self
                    .items()
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|_| core::fmt::Error)?,
            )
            .finish()
    }
}

/// An iterator yielding all the element items within an element segment.
pub struct ElementItemsIter<'a> {
    /// The amount of remaining items that this iterator will yield.
    remaining: usize,
    /// The underlying iterator from the `wasmparser` crate.
    items: wasmparser::ElementItemsReader<'a>,
}

impl<'a> From<wasmparser::ElementItemsReader<'a>> for ElementItemsIter<'a> {
    fn from(items: wasmparser::ElementItemsReader<'a>) -> Self {
        Self {
            remaining: items.get_count() as usize,
            items,
        }
    }
}

impl<'a> Iterator for ElementItemsIter<'a> {
    type Item = Result<Func, Error>;

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
                    wasmparser::ElementItem::Func(func) => {
                        let func = Func::from_raw(RawIdx::from_u32(func));
                        self.remaining -= 1;
                        Some(Ok(func))
                    }
                    wasmparser::ElementItem::Expr(_) => {
                        Err(TableError::UnsupportedExprElementItem)
                            .map_err(Into::into)
                            .into()
                    }
                }
            }
            Err(error) => Some(Err(error.into())),
        }
    }
}

impl<'a> core::iter::ExactSizeIterator for ElementItemsIter<'a> {}
impl<'a> core::iter::FusedIterator for ElementItemsIter<'a> {}
