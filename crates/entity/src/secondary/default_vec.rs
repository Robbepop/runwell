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

//! Vector-like container to associate every entity to a component that is default initialized.

use super::Immutable;
use crate::{Idx, RawIdx};
use core::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};
use std::iter::FusedIterator;

/// Container where every entity has a component that is default initialized.
///
/// This allows the default component vector to be more (space) efficient under
/// certain conditions than the normal component vector.
///
/// # Note
///
/// - Use this over a default component map if most or all of the entities require
///   their component to _NOT_ be default at some point during the program execution.
/// - The interfaces of default component data structures differ from the interfaces
///   of normal component data structures since all entities are asserted to always
///   have a component.
/// - Unbounded iteration over a default component data structure might not be what a
///   user normally wants since they eagerly iterate over the entire key space of their
///   entity which yields approx 2^32 components in total.
/// - Access to a default component data structure goes entirely through its
///   [`Index`][`core::ops::Index`] and [`IndexMut`][`core::ops::IndexMut`] implementations.
#[derive(Debug)]
pub struct DefaultComponentVec<K, V> {
    /// Stores the components at the key indices.
    ///
    /// # Note
    ///
    /// Unassigned components are set to their defaults.
    components: Vec<V>,
    /// The default prototype component.
    prototype: Immutable<V>,
    /// Type marker for the key type of the components.
    key: PhantomData<fn() -> K>,
}

impl<K, V> Clone for DefaultComponentVec<K, V>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            components: self.components.clone(),
            prototype: self.prototype.clone(),
            key: Default::default(),
        }
    }
}

impl<K, V> Default for DefaultComponentVec<K, V>
where
    V: Default,
{
    fn default() -> Self {
        Self {
            components: Default::default(),
            prototype: Default::default(),
            key: Default::default(),
        }
    }
}

impl<K, V> PartialEq for DefaultComponentVec<K, V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.components.eq(&other.components)
    }
}

impl<K, V> Eq for DefaultComponentVec<K, V> where V: Eq {}

impl<K, V> DefaultComponentVec<Idx<K>, V>
where
    V: Default,
{
    /// Converts the given key to the associated index.
    fn key_to_index(key: Idx<K>) -> usize {
        key.into_raw().into_u32() as usize
    }

    /// Returns `true` if the key is within bounds of the allocated capacity.
    fn is_within_capacity(&self, key: Idx<K>) -> bool {
        let key_at_capacity = RawIdx::from_u32(self.components.len() as u32);
        key.into_raw() < key_at_capacity
    }

    /// Enlarges the default component vector to fit the given key.
    ///
    /// Returns `true` if the secondary map actually got enlarged by the operation.
    fn set_capacity(&mut self, max_key: Idx<K>) -> bool {
        if self.is_within_capacity(max_key) {
            return false
        }
        let required_len = 1 + Self::key_to_index(max_key);
        self.components.resize_with(required_len, Default::default);
        true
    }

    /// Returns a shared reference to the entity at the key.
    fn get(&self, key: Idx<K>) -> &V {
        self.components
            .get(Self::key_to_index(key))
            .unwrap_or(&self.prototype)
    }

    /// Returns an exclusive reference to the entity at the key.
    fn get_mut(&mut self, key: Idx<K>) -> &mut V {
        self.set_capacity(key);
        &mut self.components[Self::key_to_index(key)]
    }

    /// Clears the default component vector for reusing its memory.
    pub fn clear(&mut self) {
        self.components.clear();
    }

    /// Returns an iterator yielding the components of the default component vector.
    pub fn components(&self) -> Components<Idx<K>, V> {
        Components::new(self)
    }

    /// Returns an iterator yielding the indices and components of the default component vector.
    pub fn iter(&self) -> Iter<Idx<K>, V> {
        Iter::new(self)
    }

    /// Shrinks the memory consumption of the default component vector to a minimum.
    ///
    /// # Note
    ///
    /// The operation may costly reallocate heap memory and copy its underlying components.
    pub fn shrink_to_fit(&mut self) {
        self.components.shrink_to_fit()
    }
}

impl<K, V> Index<Idx<K>> for DefaultComponentVec<Idx<K>, V>
where
    V: Default,
{
    type Output = V;

    fn index(&self, index: Idx<K>) -> &Self::Output {
        self.get(index)
    }
}

impl<K, V> IndexMut<Idx<K>> for DefaultComponentVec<Idx<K>, V>
where
    V: Default,
{
    fn index_mut(&mut self, index: Idx<K>) -> &mut Self::Output {
        self.get_mut(index)
    }
}

/// Iterator over the indices and components of a default component vector.
///
/// # Note
///
/// Unbounded iteration over a default component data structure might not be what a
/// user normally wants since they eagerly iterate over the entire key space of their
/// entity which yields approx 2^32 components in total.
pub struct Iter<'a, K, V> {
    vec: &'a DefaultComponentVec<K, V>,
    current: u32,
}

impl<'a, K, V> Iter<'a, K, V>
where
    V: Default,
{
    /// Creates a new default component vector iterator.
    fn new(vec: &'a DefaultComponentVec<K, V>) -> Self {
        Self { vec, current: 0 }
    }
}

impl<'a, K, V> Iterator for Iter<'a, Idx<K>, V>
where
    V: Default,
{
    type Item = (Idx<K>, &'a V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (RawIdx::MAX_U32 - self.current) as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == RawIdx::MAX_U32 {
            return None
        }
        let current = Idx::from_raw(RawIdx::from_u32(self.current));
        self.current += 1;
        Some((current, &self.vec[current]))
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, Idx<K>, V> where V: Default {}
impl<'a, K, V> ExactSizeIterator for Iter<'a, Idx<K>, V> where V: Default {}

/// Iterator over the components of a default component vector.
///
/// # Note
///
/// Unbounded iteration over a default component data structure might not be what a
/// user normally wants since they eagerly iterate over the entire key space of their
/// entity which yields approx 2^32 components in total.
pub struct Components<'a, K, V> {
    iter: Iter<'a, K, V>,
}

impl<'a, K, V> Components<'a, K, V>
where
    V: Default,
{
    /// Creates a new default component vector components iterator.
    fn new(vec: &'a DefaultComponentVec<K, V>) -> Self {
        Self {
            iter: Iter::new(vec),
        }
    }
}

impl<'a, K, V> Iterator for Components<'a, Idx<K>, V>
where
    V: Default,
{
    type Item = &'a V;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_idx, component)| component)
    }
}

impl<'a, K, V> FusedIterator for Components<'a, Idx<K>, V> where V: Default {}
impl<'a, K, V> ExactSizeIterator for Components<'a, Idx<K>, V> where V: Default {}
