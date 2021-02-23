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

/// A linear memory declaration.
///
/// Specifies how many initial 64 kb pages and optional maximum pages it will use.
#[derive(Debug)]
pub struct LinearMemoryDecl {
    /// The amount of pages with which the linear memory is initialized.
    initial_pages: u32,
    /// The maximum amount of pages that the linear memory will allocate.
    maximum_pages: Option<u32>,
}

impl LinearMemoryDecl {
    /// Creates a new linear memory declaration.
    pub fn new<T>(initial_pages: u32, maximum_pages: T) -> Self
    where
        T: Into<Option<u32>>,
    {
        Self {
            initial_pages,
            maximum_pages: maximum_pages.into(),
        }
    }

    /// Returns the number of initial pages.
    pub fn initial_pages(&self) -> u32 {
        self.initial_pages
    }

    /// Returns the number of maximum pages if any.
    pub fn maximum_pages(&self) -> Option<u32> {
        self.maximum_pages
    }
}

/// The initializer for a linear memory.
///
/// Initializes the contents of a linear memory at instantiation time.
#[derive(Debug, Default)]
pub struct LinearMemoryInit {
    /// Stores all data segments bytes in a contiguous buffer.
    data: Vec<u8>,
    /// Stores the lengths and offsets of all data segments.
    segments: Vec<InitSegment>,
}

/// A linear memory initialization segment.
///
/// Segments are used to initialize certain areas within a linear memory at
/// instantiation time. They may overlap and override each other upon instantiation
/// time.
#[derive(Debug)]
struct InitSegment {
    /// The length in bytes of the data segment.
    len: usize,
    /// The offset of the data segment within the linear memory.
    offset: InitExpr,
}

impl LinearMemoryInit {
    /// Pushes bytes for initialization at the offset.
    pub fn push_data<T>(&mut self, offset: InitExpr, data: T)
    where
        T: IntoIterator<Item = u8>,
    {
        let len_before = self.data.len();
        self.data.extend(data);
        let len_data = self.data.len() - len_before;
        self.segments.push(InitSegment {
            len: len_data,
            offset,
        })
    }

    /// Shrinks the internal buffers to consume less memory.
    ///
    /// Might costly reallocate internal buffers.
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
        self.segments.shrink_to_fit();
    }

    /// Iterator over the initialization segments of the linear memory initializer.
    pub fn iter(&self) -> DataSegmentIter {
        DataSegmentIter {
            data: &self.data,
            segments: self.segments.iter(),
            acc_len: 0,
        }
    }
}

impl<'a> IntoIterator for &'a LinearMemoryInit {
    type Item = (&'a InitExpr, &'a [u8]);
    type IntoIter = DataSegmentIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over the initialization segments of the linear memory initializer.
#[derive(Debug)]
pub struct DataSegmentIter<'a> {
    data: &'a [u8],
    segments: core::slice::Iter<'a, InitSegment>,
    acc_len: usize,
}

impl<'a> Iterator for DataSegmentIter<'a> {
    type Item = (&'a InitExpr, &'a [u8]);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.segments.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.segments.next() {
            Some(segment) => {
                let cursor = self.acc_len;
                let len_data = segment.len;
                let data = &self.data[cursor..(cursor + len_data)];
                self.acc_len += len_data;
                Some((&segment.offset, data))
            }
            None => None,
        }
    }
}

impl<'a> ExactSizeIterator for DataSegmentIter<'a> {}
impl<'a> FusedIterator for DataSegmentIter<'a> {}

#[cfg(test)]
mod tests {
    use super::*;
    use ir::primitive::IntConst;

    fn i32_init_expr(value: i32) -> InitExpr {
        InitExpr::Const(IntConst::I32(value).into())
    }

    #[test]
    fn init_works() {
        let offsets = [3, 0, 10];
        let data: [&[u8]; 3] =
            [&[1, 2, 3, 4][..], &[10, 20, 30][..], &[100][..]];
        let mut data_init = LinearMemoryInit::default();
        for (&offset, data) in offsets.iter().zip(data.iter().copied()) {
            data_init.push_data(i32_init_expr(offset), data.iter().copied())
        }
        data_init.shrink_to_fit();
        let mut iter = data_init.iter();
        for (&offset, data) in offsets.iter().zip(data.iter().copied()) {
            assert_eq!(iter.next(), Some((&i32_init_expr(offset), data)))
        }
        assert!(iter.next().is_none());
    }
}
