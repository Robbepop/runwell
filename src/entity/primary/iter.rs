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

use crate::entity::{Idx, RawIdx};
use core::{
    iter::{DoubleEndedIterator, FusedIterator, Zip},
    marker::PhantomData,
};

/// Iterator over the keys and shared references of their associated entity data.
#[derive(Debug)]
pub struct Iter<'a, T> {
    iter: Zip<Indices<'a, T>, Values<'a, T>>,
}

impl<'a, T> Iter<'a, T> {
    /// Creates a new shared iterator from the slice of entities.
    pub(super) fn new(
        min_key: RawIdx,
        max_key: RawIdx,
        entities: &'a [T],
    ) -> Self {
        let indices = Indices::new(min_key, max_key);
        let values = Values::new(entities);
        debug_assert_eq!(indices.size_hint(), values.size_hint());
        Self {
            iter: indices.zip(values),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Idx<T>, &'a T);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}
impl<'a, T> ExactSizeIterator for Iter<'a, T> {}

/// Iterator over the keys and exclusive references of their associated entity data.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    iter: Zip<Indices<'a, T>, ValuesMut<'a, T>>,
}

impl<'a, T> IterMut<'a, T> {
    /// Creates a new exclusive iterator from the slice of entities.
    pub(super) fn new(min_key: RawIdx, max_key: RawIdx, entities: &'a mut [T]) -> Self {
        let indices = Indices::new(min_key, max_key);
        let values = ValuesMut::new(entities);
        debug_assert_eq!(indices.size_hint(), values.size_hint());
        Self {
            iter: indices.zip(values),
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (Idx<T>, &'a mut T);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<'a, T> FusedIterator for IterMut<'a, T> {}
impl<'a, T> ExactSizeIterator for IterMut<'a, T> {}

/// Iterator yielding the indices of allocated entities in the entitiy arena.
#[derive(Debug)]
pub struct Indices<'a, T> {
    /// The current next yielded start key.
    start: u32,
    /// The current next yielded end key.
    end: u32,
    /// Required to make the data structure generic over the keys and lifetime.
    ///
    /// # Note
    ///
    /// The lifetime is important to keep the iterator in sync with Rust's
    /// borrow checker so that the iterator does not get outdated upon later
    /// mutations. Besides that the lifetime is not really needed.
    key: PhantomData<fn() -> &'a T>,
}

impl<'a, T> Indices<'a, T> {
    /// Creates a keys iterator yielding keys from start to end.
    ///
    /// # Note
    ///
    /// The `min_key` is the key to the first entity and `max_key`
    /// is the key right after the last entitiy of the entity arena.
    ///
    /// # Panics
    ///
    /// If start is not small than or equal to end.
    pub(super) fn new(min_key: RawIdx, max_key: RawIdx) -> Self {
        let start_index = min_key.into_u32();
        let end_index = max_key.into_u32();
        assert!(start_index <= end_index);
        Self {
            start: start_index,
            end: end_index,
            key: Default::default(),
        }
    }
}

impl<'a, T> Iterator for Indices<'a, T> {
    type Item = Idx<T>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start) as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let raw_idx = RawIdx::from_u32(self.start);
        self.start += 1;
        Some(Idx::from_raw(raw_idx))
    }
}

impl<'a, T> DoubleEndedIterator for Indices<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let raw_idx = RawIdx::from_u32(self.start);
        Some(Idx::from_raw(raw_idx))
    }
}

impl<'a, T> FusedIterator for Indices<'a, T> {}
impl<'a, T> ExactSizeIterator for Indices<'a, T> {}

/// Iterator yielding shared references to allocated values of the entitiy arena.
#[derive(Debug)]
pub struct Values<'a, T> {
    iter: core::slice::Iter<'a, T>,
}

impl<'a, T> Values<'a, T> {
    /// Creates a values iterator yielding the allocated entities of an entity arena.
    pub(super) fn new(entities: &'a [T]) -> Self {
        Self {
            iter: entities.iter(),
        }
    }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n)
    }
}

impl<'a, T> DoubleEndedIterator for Values<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth_back(n)
    }
}

impl<'a, T> FusedIterator for Values<'a, T> {}
impl<'a, T> ExactSizeIterator for Values<'a, T> {}

/// Iterator yielding mutable reference to allocated values of the entitiy arena.
#[derive(Debug)]
pub struct ValuesMut<'a, T> {
    iter: core::slice::IterMut<'a, T>,
}

impl<'a, T> ValuesMut<'a, T> {
    /// Creates a values iterator yielding the allocated entities of an entity arena.
    pub(super) fn new(entities: &'a mut [T]) -> Self {
        Self {
            iter: entities.iter_mut(),
        }
    }
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n)
    }
}

impl<'a, T> DoubleEndedIterator for ValuesMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth_back(n)
    }
}

impl<'a, T> FusedIterator for ValuesMut<'a, T> {}
impl<'a, T> ExactSizeIterator for ValuesMut<'a, T> {}
