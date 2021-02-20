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

//! Vector-like data structure to efficiently associate a single bit as component for an entity.

use crate::{Idx, RawIdx};
use core::{iter::FusedIterator, marker::PhantomData};
use smallbitvec::SmallBitVec;

/// Container where every entity has a `bool` component that is default initialized to `false`.
///
/// # Note
///
/// - Use this if you need to store `bool` types as components for your entities efficient
///   and expect most of the entities to have this component.
/// - Prefer using this data structure if the `bool` components are likely `false` (default)
///   for most entities.
/// - The API of the `DefaultComponentBitVec` differs slightly from the `DefaultComponentVec`
///   because it is not very useful to have `bool` references which hinders implementing
///   the common `Index` and `IndexMut` traits. Use the `get` and `set` methods of the
///   `DefaultComponentBitVec` type instead respectively.
/// - Unbounded iteration over a default component data structure might not be what a
///   user normally wants since they eagerly iterate over the entire key space of their
///   entity which yields approx 2^32 components in total.
#[derive(Debug)]
pub struct DefaultComponentBitVec<K> {
    /// Stores the `bool` components at the key indices.
    ///
    /// # Note
    ///
    /// Unassigned bits are set to `false`.
    components: SmallBitVec,
    /// Type marker for the key type of the components.
    key: PhantomData<fn() -> K>,
}

impl<K> Clone for DefaultComponentBitVec<K> {
    fn clone(&self) -> Self {
        Self {
            components: self.components.clone(),
            key: Default::default(),
        }
    }
}

impl<K> Default for DefaultComponentBitVec<K> {
    fn default() -> Self {
        Self {
            components: Default::default(),
            key: Default::default(),
        }
    }
}

impl<K> PartialEq for DefaultComponentBitVec<K> {
    fn eq(&self, other: &Self) -> bool {
        self.components.eq(&other.components)
    }
}

impl<K> Eq for DefaultComponentBitVec<K> {}

impl<K> DefaultComponentBitVec<Idx<K>> {
    /// Reserves the minimum capacity for exactly `additional` more components to be
    /// inserted in the component data structure.
    ///
    /// Does nothing if capacity is already sufficient.
    pub fn reserve_exact(&mut self, additional: u32) {
        assert!(
            additional as usize + self.components.capacity()
                <= RawIdx::MAX_U32 as usize
        );
        self.components.reserve(additional as usize);
    }

    /// Converts the given key to the associated index.
    fn key_to_index(key: Idx<K>) -> usize {
        key.into_raw().into_u32() as usize
    }

    /// Returns `true` if the key is within bounds of the allocated capacity.
    fn is_within_capacity(&self, key: Idx<K>) -> bool {
        let key_at_capacity = RawIdx::from_u32(self.components.len() as u32);
        key.into_raw() < key_at_capacity
    }

    /// Enlarges the default component bit-vector to fit the given key.
    ///
    /// Returns `true` if the underlying vector actually got enlarged by the operation.
    fn set_capacity(&mut self, max_key: Idx<K>) -> bool {
        if self.is_within_capacity(max_key) {
            return false
        }
        let required_len = 1 + Self::key_to_index(max_key);
        self.components.resize(required_len, false);
        true
    }

    /// Returns the current `bool` value of the key'ed entitiy.
    ///
    /// Returns `false` if the component is not yet set for the entitiy.
    #[inline]
    pub fn get(&self, key: Idx<K>) -> bool {
        self.components
            .get(Self::key_to_index(key))
            .unwrap_or(false)
    }

    /// Sets the `bool` component of the key'ed entity to the `new_value`.
    #[inline]
    pub fn set(&mut self, key: Idx<K>, new_value: bool) {
        self.set_capacity(key);
        self.components.set(Self::key_to_index(key), new_value);
    }

    /// Replaces the current `bool` value (if any) of the entity with the `new_value`.
    ///
    /// Returns the old `bool` value of `false` if there was no component set before.
    #[inline]
    pub fn replace(&mut self, key: Idx<K>, new_value: bool) -> bool {
        let old_value = self.get(key);
        self.set(key, new_value);
        old_value
    }

    /// Clears the default component bit-vector for reusing its memory.
    pub fn clear(&mut self) {
        self.components.clear();
    }

    /// Returns an iterator yielding the components of the default component bit-vector.
    pub fn components(&self) -> Components<K> {
        Components::new(self)
    }

    /// Returns an iterator yielding the indices and components of the default component bit-vector.
    pub fn iter(&self) -> Iter<K> {
        Iter::new(self)
    }

    /// Shrinks the memory consumption of the default component bit-vector to a minimum.
    ///
    /// # Note
    ///
    /// The operation may costly reallocate heap memory and copy its underlying components.
    pub fn shrink_to_fit(&mut self) {
        // The `smallbitvec::SmallBitvec` types does not support `shrink_to_fit` so we do
        // nothing instead since minimizing heap memory usage is not guaranteed by this API.
    }
}

/// Iterator over the indices and components of a default component bit-vector.
///
/// # Note
///
/// Unbounded iteration over a default component data structure might not be what a
/// user normally wants since they eagerly iterate over the entire key space of their
/// entity which yields approx 2^32 components in total.
pub struct Iter<'a, K> {
    vec: &'a DefaultComponentBitVec<Idx<K>>,
    current: u32,
}

impl<'a, K> Iter<'a, K> {
    /// Creates a new default component vector iterator.
    fn new(vec: &'a DefaultComponentBitVec<Idx<K>>) -> Self {
        Self { vec, current: 0 }
    }
}

impl<'a, K> Iterator for Iter<'a, K> {
    type Item = (Idx<K>, bool);

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
        Some((current, self.vec.get(current)))
    }
}

impl<'a, K> FusedIterator for Iter<'a, K> {}
impl<'a, K> ExactSizeIterator for Iter<'a, K> {}

/// Iterator over the components of a default component vector.
///
/// # Note
///
/// Unbounded iteration over a default component data structure might not be what a
/// user normally wants since they eagerly iterate over the entire key space of their
/// entity which yields approx 2^32 components in total.
pub struct Components<'a, K> {
    iter: Iter<'a, K>,
}

impl<'a, K> Components<'a, K> {
    /// Creates a new default component vector components iterator.
    fn new(vec: &'a DefaultComponentBitVec<Idx<K>>) -> Self {
        Self {
            iter: Iter::new(vec),
        }
    }
}

impl<'a, K> Iterator for Components<'a, K> {
    type Item = bool;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_idx, component)| component)
    }
}

impl<'a, K> FusedIterator for Components<'a, K> {}
impl<'a, K> ExactSizeIterator for Components<'a, K> {}
