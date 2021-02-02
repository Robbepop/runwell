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

use crate::init_expr::InitExpr;
use core::iter::FusedIterator;
use ir::primitive::Func;

/// A table declaration.
///
/// Tables are used to store function references for indirect function dispatches.
#[derive(Debug)]
pub struct TableDecl {
    /// The capacity with which the table is initialized.
    initial_size: u32,
    /// The maximum capacity that the table will allocate.
    maximum_size: Option<u32>,
}

impl TableDecl {
    /// Creates a new table declaration.
    pub fn new<T>(initial_size: u32, maximum_size: T) -> Self
    where
        T: Into<Option<u32>>,
    {
        Self {
            initial_size,
            maximum_size: maximum_size.into(),
        }
    }

    /// Returns the initial capacity for table elements.
    pub fn initial_size(&self) -> u32 {
        self.initial_size
    }

    /// Returns the maximum capacity for table elements if any.
    pub fn maximum_size(&self) -> Option<u32> {
        self.maximum_size
    }
}

/// The initializer for a table.
///
/// Initializes the contents of a table at instantiation time.
#[derive(Debug, Default)]
pub struct TableInit {
    /// Stores all element segment function references in a contiguous buffer.
    element: Vec<Func>,
    /// Stores the lengths and offsets of all element segments.
    segments: Vec<InitSegment>,
}

/// A table initialization segment.
///
/// Segments are used to initialize certain areas within a table at
/// instantiation time. They may overlap and override each other upon instantiation
/// time.
#[derive(Debug)]
struct InitSegment {
    /// The length in bytes of the element segment.
    len: usize,
    /// The offset of the element segment within the table.
    offset: InitExpr,
}

impl TableInit {
    /// Pushes bytes for initialization at the offset.
    pub fn push_element<T>(&mut self, offset: InitExpr, funcs: T)
    where
        T: IntoIterator<Item = Func>,
    {
        let len_before = self.element.len();
        self.element.extend(funcs);
        let len_element = self.element.len() - len_before;
        self.segments.push(InitSegment {
            len: len_element,
            offset,
        })
    }

    /// Shrinks the internal buffers to consume less memory.
    ///
    /// Might costly reallocate internal buffers.
    pub fn shrink_to_fit(&mut self) {
        self.element.shrink_to_fit();
        self.segments.shrink_to_fit();
    }

    /// Iterator over the initialization segments of the table initializer.
    pub fn iter(&self) -> ElementSegmentIter {
        ElementSegmentIter {
            element: &self.element,
            segments: self.segments.iter(),
            acc_len: 0,
        }
    }
}

impl<'a> IntoIterator for &'a TableInit {
    type Item = (&'a InitExpr, &'a [Func]);
    type IntoIter = ElementSegmentIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over the initialization segments of the table initializer.
#[derive(Debug)]
pub struct ElementSegmentIter<'a> {
    element: &'a [Func],
    segments: core::slice::Iter<'a, InitSegment>,
    acc_len: usize,
}

impl<'a> Iterator for ElementSegmentIter<'a> {
    type Item = (&'a InitExpr, &'a [Func]);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.segments.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.segments.next() {
            Some(segment) => {
                let cursor = self.acc_len;
                let len_element = segment.len;
                let element = &self.element[cursor..(cursor + len_element)];
                self.acc_len += len_element;
                Some((&segment.offset, element))
            }
            None => None,
        }
    }
}

impl<'a> ExactSizeIterator for ElementSegmentIter<'a> {}
impl<'a> FusedIterator for ElementSegmentIter<'a> {}

#[cfg(test)]
mod tests {
    use super::*;
    use entity::RawIdx;
    use ir::primitive::IntConst;

    fn i32_init_expr(value: i32) -> InitExpr {
        InitExpr::Const(IntConst::I32(value).into())
    }

    fn func(value: u32) -> Func {
        Func::from_raw(RawIdx::from_u32(value))
    }

    #[test]
    fn init_works() {
        let offsets = [3, 0, 10];
        let funcs = [
            &[func(1), func(2), func(3), func(4)][..],
            &[func(10), func(20), func(30)][..],
            &[func(100)][..],
        ];
        let mut table_init = TableInit::default();
        for (&offset, funcs) in offsets.iter().zip(funcs.iter().copied()) {
            table_init
                .push_element(i32_init_expr(offset), funcs.iter().copied())
        }
        table_init.shrink_to_fit();
        let mut iter = table_init.iter();
        for (&offset, funcs) in offsets.iter().zip(funcs.iter().copied()) {
            assert_eq!(iter.next(), Some((&i32_init_expr(offset), funcs)))
        }
        assert!(iter.next().is_none());
    }
}
