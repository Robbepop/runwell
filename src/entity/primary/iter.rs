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
