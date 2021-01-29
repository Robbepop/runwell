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

//! Map-like container to associate every entity to a component that is default initialized.

use super::Immutable;
use crate::{Idx, RawIdx};
use core::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};
use std::{collections::HashMap, iter::FusedIterator};

/// Container where every entity has a component that is default initialized.
///
/// This allows the default component map to be more (space) efficient under
/// certain conditions than the normal component map.
///
/// # Note
///
/// - Use this over a default component vector if only a few of the entities require
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
pub struct DefaultComponentMap<K, V> {
    /// Stores the components at the key indices.
    ///
    /// # Note
    ///
    /// Unassigned components are set to their defaults.
    components: HashMap<RawIdx, V, ahash::RandomState>,
    /// The default prototype component.
    prototype: Immutable<V>,
    /// Type marker for the key type of the components.
    key: PhantomData<fn() -> K>,
}

impl<K, V> Clone for DefaultComponentMap<K, V>
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

impl<K, V> Default for DefaultComponentMap<K, V>
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

impl<K, V> PartialEq for DefaultComponentMap<K, V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.components.eq(&other.components)
    }
}

impl<K, V> Eq for DefaultComponentMap<K, V> where V: Eq {}

impl<K, V> DefaultComponentMap<Idx<K>, V>
where
    V: Default,
{
    /// Returns a shared reference to the entity at the key.
    fn get(&self, key: Idx<K>) -> &V {
        self.components
            .get(&key.into_raw())
            .unwrap_or(&self.prototype)
    }

    /// Returns an exclusive reference to the entity at the key.
    fn get_mut(&mut self, key: Idx<K>) -> &mut V {
        self.components.entry(key.into_raw()).or_default()
    }

    /// Clears the default component vector for reusing its memory.
    #[inline]
    pub fn clear(&mut self) {
        self.components.clear();
    }

    /// Returns an iterator yielding the components of the default component vector.
    pub fn components(&self) -> Components<K, V> {
        Components::new(self)
    }

    /// Returns an iterator yielding the indices and components of the default component vector.
    pub fn iter(&self) -> Iter<K, V> {
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

impl<K, V> Index<Idx<K>> for DefaultComponentMap<Idx<K>, V>
where
    V: Default,
{
    type Output = V;

    #[inline]
    fn index(&self, index: Idx<K>) -> &Self::Output {
        self.get(index)
    }
}

impl<K, V> IndexMut<Idx<K>> for DefaultComponentMap<Idx<K>, V>
where
    V: Default,
{
    #[inline]
    fn index_mut(&mut self, index: Idx<K>) -> &mut Self::Output {
        self.get_mut(index)
    }
}

impl<'a, K, V> IntoIterator for &'a DefaultComponentMap<Idx<K>, V>
where
    V: Default,
{
    type Item = (Idx<K>, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over the indices and components of a default component map.
///
/// # Note
///
/// Unbounded iteration over a default component data structure might not be what a
/// user normally wants since they eagerly iterate over the entire key space of their
/// entity which yields approx 2^32 components in total.
pub struct Iter<'a, K, V> {
    vec: &'a DefaultComponentMap<Idx<K>, V>,
    current: u32,
}

impl<'a, K, V> Iter<'a, K, V>
where
    V: Default,
{
    /// Creates a new default component map iterator.
    fn new(vec: &'a DefaultComponentMap<Idx<K>, V>) -> Self {
        Self { vec, current: 0 }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
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

impl<'a, K, V> FusedIterator for Iter<'a, K, V> where V: Default {}
impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> where V: Default {}

/// Iterator over the components of a default component map.
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
    /// Creates a new default component map components iterator.
    fn new(vec: &'a DefaultComponentMap<Idx<K>, V>) -> Self {
        Self {
            iter: Iter::new(vec),
        }
    }
}

impl<'a, K, V> Iterator for Components<'a, K, V>
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

impl<'a, K, V> FusedIterator for Components<'a, K, V> where V: Default {}
impl<'a, K, V> ExactSizeIterator for Components<'a, K, V> where V: Default {}
