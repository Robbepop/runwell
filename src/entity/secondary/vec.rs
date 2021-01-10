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
    iter::FusedIterator,
    marker::PhantomData,
    mem::replace,
    ops::{Index, IndexMut},
};

/// Dense secondary map to associated new components for existing entities.
///
/// # Efficiency
///
/// Very efficient if the component is very common for the entities.
/// Might be slow for iteration and wastes a lot of space if only a few entities
/// have the component.
///
/// # Note
///
/// - The component vector is well suited when a component is very common for entities.
/// - By design all secondary component containers are meant to be easily interchangable.
pub struct ComponentVec<K, V> {
    /// Stores the components at the key indices.
    ///
    /// # Note
    ///
    /// If a key does not have a component the entry is `None`.
    components: Vec<Option<V>>,
    /// The number of actual components in the vector.
    ///
    /// # Note
    ///
    /// This number is equal to the number of `Some` items in the `components` vector.
    len_some: usize,
    /// Type marker for the key type of the components.
    key: PhantomData<fn() -> K>,
}

impl<K, V> Clone for ComponentVec<K, V>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            components: self.components.clone(),
            len_some: self.len_some,
            key: Default::default(),
        }
    }
}

impl<K, V> Default for ComponentVec<K, V> {
    fn default() -> Self {
        Self {
            components: Default::default(),
            len_some: 0,
            key: Default::default(),
        }
    }
}

impl<K, V> ComponentVec<K, V>
where
    K: Index32,
{
    /// Converts the given key to the associated index.
    fn key_to_index(key: K) -> usize {
        key.into_u32() as usize
    }

    /// Returns `true` if the key is valid for the secondary map.
    ///
    /// If the key is invalid the secondary map has to be enlarged to fit the key.
    pub fn contains_key(&self, key: K) -> bool {
        self.components
            .get(Self::key_to_index(key))
            .map(Option::is_some)
            .unwrap_or(false)
    }

    /// Returns the number of components in the secondary map.
    pub fn len(&self) -> usize {
        self.len_some
    }

    /// Returns `true` if there are no components in the secondary map.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Enlarges the component vector to fit the given key.
    ///
    /// Returns `true` if the secondary map actually got enlarged by the operation.
    fn enlarge_for(&mut self, max_key: K) -> bool {
        if self.contains_key(max_key) {
            return false
        }
        let required_len = 1 + Self::key_to_index(max_key);
        self.components.resize_with(required_len, || None);
        true
    }

    /// Inserts the component for the key and returns the previous component if any.
    pub fn insert(&mut self, key: K, component: V) -> Option<V> {
        self.enlarge_for(key);
        let old_component = replace(
            &mut self.components[Self::key_to_index(key)],
            Some(component),
        );
        self.len_some += old_component.is_none() as usize;
        old_component
    }

    /// Removes the component for the key and returns the removed component if any.
    pub fn remove(&mut self, key: K) -> Option<V> {
        if !self.contains_key(key) {
            return None
        }
        let removed_component =
            replace(&mut self.components[Self::key_to_index(key)], None);
        self.len_some -= removed_component.is_some() as usize;
        removed_component
    }

    /// Returns a shared reference to the entity at the key.
    pub fn get(&self, key: K) -> Option<&V> {
        self.components
            .get(Self::key_to_index(key))
            .and_then(Into::into)
    }

    /// Returns an exclusive reference to the entity at the key.
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.components
            .get_mut(Self::key_to_index(key))
            .and_then(Into::into)
    }

    /// Returns an iterator over the keys and shared references to their associated data.
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.components.iter(),
            start: 0,
            remaining: self.len_some,
            key: Default::default(),
        }
    }

    /// Returns an iterator over the keys and exclusive references to their associated data.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.components.iter_mut(),
            start: 0,
            remaining: self.len_some,
            key: Default::default(),
        }
    }

    /// Clears the component vector for reusing its memory.
    pub fn clear(&mut self) {
        self.components.clear();
        self.len_some = 0;
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        match self.get(key) {
            Some(_) => Entry::Occupied(OccupiedEntry { vec: self, key }),
            None => Entry::Vacant(VacantEntry { vec: self, key }),
        }
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This enum is constructed from the entry method on `ComponentVec`.
pub enum Entry<'a, K: 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Index32,
{
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
    pub fn key(&self) -> K {
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
    K: Index32,
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

/// A view into an occupied entry in a `ComponentVec`. It is part of the `Entry` enum.
pub struct OccupiedEntry<'a, K, V> {
    vec: &'a mut ComponentVec<K, V>,
    key: K,
}

const UNEXPECTED_VACANT_COMPONENT: &str =
    "unexpected vacant component for occupied entry";

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: Index32,
{
    /// Returns the key from the entry.
    pub fn key(&self) -> K {
        self.key
    }

    /// Take the ownership of the key and value from the map.
    pub fn remove_entry(self) -> (K, V) {
        let key = self.key;
        let old_component = self.remove();
        (key, old_component)
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        self.vec.components[<ComponentVec<K, V>>::key_to_index(self.key)]
            .as_ref()
            .expect(UNEXPECTED_VACANT_COMPONENT)
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see `into_mut`.
    pub fn get_mut(&mut self) -> &mut V {
        self.vec.components[<ComponentVec<K, V>>::key_to_index(self.key)]
            .as_mut()
            .expect(UNEXPECTED_VACANT_COMPONENT)
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see `get_mut`.
    pub fn into_mut(self) -> &'a mut V {
        self.vec.components[<ComponentVec<K, V>>::key_to_index(self.key)]
            .as_mut()
            .expect(UNEXPECTED_VACANT_COMPONENT)
    }

    /// Sets the value of the entry, and returns the entry's old value.
    pub fn insert(&mut self, component: V) -> V {
        self.vec
            .insert(self.key, component)
            .expect(UNEXPECTED_VACANT_COMPONENT)
    }

    /// Takes the value out of the entry, and returns it.
    pub fn remove(self) -> V {
        self.vec
            .remove(self.key)
            .expect(UNEXPECTED_VACANT_COMPONENT)
    }
}

/// A view into a vacant entry in a `ComponentVec`. It is part of the `Entry` enum.
pub struct VacantEntry<'a, K, V> {
    vec: &'a mut ComponentVec<K, V>,
    key: K,
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Index32,
{
    /// Returns the key that would be used when inserting a value through the `VacantEntry`.
    pub fn key(&self) -> K {
        self.key
    }

    /// Sets the value of the entry with the VacantEntry's key, and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        self.vec.insert(self.key, value);
        self.vec.components[<ComponentVec<K, V>>::key_to_index(self.key)]
            .as_mut()
            .expect("unexpected missing component that has just been inserted")
    }
}

impl<K, V> Index<K> for ComponentVec<K, V>
where
    K: Index32,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(index)
            .expect("invalid key for densely stored component")
    }
}

impl<K, V> IndexMut<K> for ComponentVec<K, V>
where
    K: Index32,
{
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.get_mut(index)
            .expect("invalid key for densely stored component")
    }
}

/// Iterator yielding contained keys and shared references to their components.
pub struct Iter<'a, K, V> {
    iter: core::slice::Iter<'a, Option<V>>,
    start: u32,
    remaining: usize,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Index32,
{
    type Item = (K, &'a V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.remaining == 0 {
                return None
            }
            match self.iter.next() {
                Some(maybe_component) => {
                    let key = K::from_u32(self.start);
                    self.start += 1;
                    if let Some(component) = maybe_component {
                        self.remaining -= 1;
                        return Some((key, component))
                    }
                    continue
                }
                None => return None,
            }
        }
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> where K: Index32 {}
impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> where K: Index32 {}

/// Iterator yielding contained keys and exclusive references to their components.
pub struct IterMut<'a, K, V> {
    iter: core::slice::IterMut<'a, Option<V>>,
    start: u32,
    remaining: usize,
    key: PhantomData<fn() -> K>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: Index32,
{
    type Item = (K, &'a mut V);

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.remaining == 0 {
                return None
            }
            match self.iter.next() {
                Some(maybe_component) => {
                    let key = K::from_u32(self.start);
                    self.start += 1;
                    if let Some(component) = maybe_component {
                        self.remaining -= 1;
                        return Some((key, component))
                    }
                    continue
                }
                None => return None,
            }
        }
    }
}

impl<'a, K, V> FusedIterator for IterMut<'a, K, V> where K: Index32 {}
impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> where K: Index32 {}
