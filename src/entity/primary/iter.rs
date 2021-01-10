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

use crate::Index32;
use core::{
    iter::{DoubleEndedIterator, FusedIterator},
    marker::PhantomData,
};

pub struct Iter<'a, K, V> {
    iter: core::slice::Iter<'a, V>,
    start: u32,
    end: u32,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> Iter<'a, K, V> {
    /// Creates a new shared iterator from the slice of entities.
    pub(super) fn new(entities: &'a [V]) -> Self {
        Self {
            iter: entities.iter(),
            start: 0,
            end: entities.len() as u32,
            key: Default::default(),
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Index32,
{
    type Item = (K, &'a V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        let entity = self.iter.next()?;
        let key = K::from_u32(self.start);
        self.start += 1;
        Some((key, entity))
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V>
where
    K: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let entity = self.iter.next_back()?;
        self.end -= 1;
        let key = K::from_u32(self.end);
        Some((key, entity))
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> where K: Index32 {}
impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> where K: Index32 {}

pub struct IterMut<'a, K, V> {
    iter: core::slice::IterMut<'a, V>,
    start: u32,
    end: u32,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    /// Creates a new exclusive iterator from the slice of entities.
    pub(super) fn new(entities: &'a mut [V]) -> Self {
        let end = entities.len() as u32;
        Self {
            iter: entities.iter_mut(),
            start: 0,
            end,
            key: Default::default(),
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: Index32,
{
    type Item = (K, &'a mut V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        let entity = self.iter.next()?;
        let key = K::from_u32(self.start);
        self.start += 1;
        Some((key, entity))
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V>
where
    K: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let entity = self.iter.next_back()?;
        self.end -= 1;
        let key = K::from_u32(self.end);
        Some((key, entity))
    }
}

impl<'a, K, V> FusedIterator for IterMut<'a, K, V> where K: Index32 {}
impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> where K: Index32 {}

/// Iterator yielding the keys of the entitiy arena.
pub struct Keys<'a, K> {
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
    key: PhantomData<fn() -> &'a K>,
}

impl<'a, K> Keys<'a, K>
where
    K: Index32,
{
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
    pub(super) fn new(min_key: K, max_key: K) -> Self {
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

impl<'a, K> Iterator for Keys<'a, K>
where
    K: Index32,
{
    type Item = K;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start) as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let key = K::from_u32(self.start);
        self.start += 1;
        Some(key)
    }
}

impl<'a, K> DoubleEndedIterator for Keys<'a, K>
where
    K: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let key = K::from_u32(self.end);
        Some(key)
    }
}

impl<'a, K> FusedIterator for Keys<'a, K> where K: Index32 {}
impl<'a, K> ExactSizeIterator for Keys<'a, K> where K: Index32 {}
