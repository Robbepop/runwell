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

use crate::parse::{CompilerError, FunctionId, InitializerExpr};

/// The elements with which a Wasm table has been initialized.
///
/// This is a mapping from an index to a function reference.
/// Value types besides function references are not yet supported.
#[derive(Debug, Default)]
pub struct TableElements {
    elements: Vec<Element>,
}

impl TableElements {
    /// Pushes another element to the table.
    ///
    /// An element is comprised of an offset expression as well as
    /// some element items that have their indices shifted by the
    /// offset and are layed out consecutively in the table.
    pub fn push_element<I>(
        &mut self,
        offset: InitializerExpr,
        items: I,
    ) -> Result<(), CompilerError>
    where
        I: IntoIterator<Item = FunctionId>,
    {
        self.elements.push(Element {
            offset,
            items: items.into_iter().collect(),
        });
        Ok(())
    }
}

/// An element from the Wasm element section assigned to a table.
#[derive(Debug)]
pub struct Element {
    /// The offset expression of the element.
    offset: InitializerExpr,
    /// The items of the element.
    items: Vec<FunctionId>,
}
