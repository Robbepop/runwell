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

//! Container to associate some entities to components in a sparse representation.

use crate::{Idx, RawIdx};
use core::{
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Index, IndexMut},
};
use std::collections::{
    hash_map::{
        self,
        Iter as HashMapIter,
        IterMut as HashMapIterMut,
        Values as HashMapValues,
        ValuesMut as HashMapValuesMut,
    },
    HashMap,
};

/// Sparse secondary map to associated new components for existing entities.
///
/// # Efficiency
///
/// Very efficient if the component is very uncommon for the entities.
/// Might be less efficient than optimal for common operations if too many entities
/// have the component.
///
///
/// # Note
///
/// - The component map is well suited when only few entities have a component.
/// - By design all secondary component containers are meant to be easily interchangeable.
#[derive(Debug)]
pub struct ComponentMap<K, V> {
    components: HashMap<RawIdx, V, ahash::RandomState>,
    key: PhantomData<fn() -> K>,
}

impl<K, V> Clone for ComponentMap<K, V>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            components: self.components.clone(),
            key: Default::default(),
        }
    }
}

impl<K, V> Default for ComponentMap<K, V> {
    fn default() -> Self {
        Self {
            components: Default::default(),
            key: Default::default(),
        }
    }
}

impl<K, V> PartialEq for ComponentMap<K, V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.components.eq(&other.components)
    }
}

impl<K, V> Eq for ComponentMap<K, V> where V: Eq {}

impl<K, V> ComponentMap<Idx<K>, V> {
    /// Reserves the minimum capacity for exactly `additional` more elements to be
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

    /// Returns `true` if the key is valid for the secondary map.
    ///
    /// If the key is invalid the secondary map has to be enlarged to fit the key.
    #[inline]
    pub fn contains_key(&self, key: Idx<K>) -> bool {
        self.components.contains_key(&key.into_raw())
    }

    /// Returns the number of components in the secondary map.
    #[inline]
    pub fn len(&self) -> usize {
        self.components.len()
    }

    /// Returns `true` if there are no components in the secondary map.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.components.is_empty()
    }

    /// Inserts the component for the key and returns the previous component if any.
    #[inline]
    pub fn insert(&mut self, key: Idx<K>, component: V) -> Option<V> {
        self.components.insert(key.into_raw(), component)
    }

    /// Removes the components for the key and returns the removed component if any.
    #[inline]
    pub fn remove(&mut self, key: Idx<K>) -> Option<V> {
        self.components.remove(&key.into_raw())
    }

    /// Returns a shared reference to the component at the given key.
    #[inline]
    pub fn get(&self, key: Idx<K>) -> Option<&V> {
        self.components.get(&key.into_raw())
    }

    /// Returns a exclusive reference to the component at the given key.
    #[inline]
    pub fn get_mut(&mut self, key: Idx<K>) -> Option<&mut V> {
        self.components.get_mut(&key.into_raw())
    }

    /// Returns an iterator over shared references to the components.
    pub fn components(&self) -> Components<V> {
        Components {
            iter: self.components.values(),
        }
    }

    /// Returns an iterator over mutable references to the components.
    pub fn components_mut(&mut self) -> ComponentsMut<V> {
        ComponentsMut {
            iter: self.components.values_mut(),
        }
    }

    /// Returns an iterator over the keys and a shared reference to their associated components.
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.components.iter(),
            key: Default::default(),
        }
    }

    /// Returns an iterator over the keys and an exclusive reference to their associated components.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.components.iter_mut(),
            key: Default::default(),
        }
    }

    /// Clears the component map for reusing its memory.
    pub fn clear(&mut self) {
        self.components.clear();
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    #[inline]
    pub fn entry(&mut self, key: Idx<K>) -> Entry<K, V> {
        let key_index = key.into_raw();
        match self.components.entry(key_index) {
            hash_map::Entry::Occupied(occupied) => {
                Entry::Occupied(OccupiedEntry {
                    occupied,
                    key: Default::default(),
                })
            }
            hash_map::Entry::Vacant(vacant) => {
                Entry::Vacant(VacantEntry {
                    vacant,
                    key: Default::default(),
                })
            }
        }
    }

    /// Shrinks the memory consumption of the component map to a minimum.
    ///
    /// # Note
    ///
    /// The operation may costly reallocate heap memory and copy its underlying components.
    pub fn shrink_to_fit(&mut self) {
        self.components.shrink_to_fit()
    }
}

impl<K, V> Index<Idx<K>> for ComponentMap<Idx<K>, V> {
    type Output = V;

    #[inline]
    fn index(&self, index: Idx<K>) -> &Self::Output {
        self.get(index)
            .expect("invalid key for sparsely stored component")
    }
}

impl<K, V> IndexMut<Idx<K>> for ComponentMap<Idx<K>, V> {
    #[inline]
    fn index_mut(&mut self, index: Idx<K>) -> &mut Self::Output {
        self.get_mut(index)
            .expect("invalid key for sparsely stored component")
    }
}

impl<'a, K, V> IntoIterator for &'a ComponentMap<Idx<K>, V> {
    type Item = (Idx<K>, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut ComponentMap<Idx<K>, V> {
    type Item = (Idx<K>, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the entry method on `ComponentMap`.
#[derive(Debug)]
pub enum Entry<'a, K: 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(move || default)
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => vacant.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
    pub fn key(&self) -> Idx<K> {
        match self {
            Entry::Occupied(occupied) => occupied.key(),
            Entry::Vacant(vacant) => vacant.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut occupied) => {
                f(occupied.get_mut());
                Entry::Occupied(occupied)
            }
            Entry::Vacant(vacant) => Entry::Vacant(vacant),
        }
    }
}

impl<'a, K, V> Entry<'a, K, V>
where
    V: Default,
{
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => vacant.insert(Default::default()),
        }
    }
}

/// A view into an occupied entry in a `ComponentMap`. It is part of the `Entry` `enum`.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K, V> {
    occupied: hash_map::OccupiedEntry<'a, RawIdx, V>,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Returns the key from the entry.
    pub fn key(&self) -> Idx<K> {
        Idx::from_raw(*self.occupied.key())
    }

    /// Take the ownership of the key and value from the map.
    pub fn remove_entry(self) -> (Idx<K>, V) {
        let (key, component) = self.occupied.remove_entry();
        (Idx::from_raw(key), component)
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        self.occupied.get()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see `into_mut`.
    pub fn get_mut(&mut self) -> &mut V {
        self.occupied.get_mut()
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see `get_mut`.
    pub fn into_mut(self) -> &'a mut V {
        self.occupied.into_mut()
    }

    /// Sets the value of the entry, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        self.occupied.insert(value)
    }

    /// Takes the value out of the entry, and returns it.
    pub fn remove(self) -> V {
        self.occupied.remove()
    }
}

/// A view into a vacant entry in a `ComponentMap`. It is part of the `Entry` `enum`.
#[derive(Debug)]
pub struct VacantEntry<'a, K, V> {
    vacant: hash_map::VacantEntry<'a, RawIdx, V>,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    /// Returns the key that would be used when inserting a value through the `VacantEntry`.
    pub fn key(&self) -> Idx<K> {
        Idx::from_raw(*self.vacant.key())
    }

    /// Sets the value of the entry with the vacant entry's key, and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        self.vacant.insert(value)
    }
}

/// Iterator yielding shared references to the components.
#[derive(Debug)]
pub struct Components<'a, V> {
    iter: HashMapValues<'a, RawIdx, V>,
}

impl<'a, V> Iterator for Components<'a, V> {
    type Item = &'a V;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, V> ExactSizeIterator for Components<'a, V> {}
impl<'a, V> FusedIterator for Components<'a, V> {}

/// Iterator yielding mutable references to the components.
#[derive(Debug)]
pub struct ComponentsMut<'a, V> {
    iter: HashMapValuesMut<'a, RawIdx, V>,
}

impl<'a, V> Iterator for ComponentsMut<'a, V> {
    type Item = &'a mut V;

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, V> ExactSizeIterator for ComponentsMut<'a, V> {}
impl<'a, V> FusedIterator for ComponentsMut<'a, V> {}

/// Iterator yielding keys and a shared reference to their associated components.
#[derive(Debug)]
pub struct Iter<'a, K, V> {
    iter: HashMapIter<'a, RawIdx, V>,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (Idx<K>, &'a V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(key, component)| (Idx::from_raw(*key), component))
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}
impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}

/// Iterator yielding keys and an exclusive reference to their associated components.
#[derive(Debug)]
pub struct IterMut<'a, K, V> {
    iter: HashMapIterMut<'a, RawIdx, V>,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (Idx<K>, &'a mut V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(key, component)| (Idx::from_raw(*key), component))
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {}
impl<'a, K, V> FusedIterator for IterMut<'a, K, V> {}
