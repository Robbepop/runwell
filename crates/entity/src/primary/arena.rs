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

use super::iter::{Entities, EntitiesMut, Indices, Iter, IterMut};
use crate::{Idx, RawIdx};
use core::{
    iter::FromIterator,
    ops::{Index, IndexMut},
};

/// Primary map to create new entities and store required data for them.
///
/// # Note
///
/// Use this if all your entities are required to store some additional necessary
/// information or data with them or if the data identifies the entity.
///
/// For efficiency and satety reasons it is not possible to remove entities.
#[derive(Debug, Clone)]
pub struct EntityArena<T> {
    entities: Vec<T>,
}

impl<T> Default for EntityArena<T> {
    fn default() -> Self {
        Self {
            entities: Default::default(),
        }
    }
}

impl<T> EntityArena<T>
where
    T: Default,
{
    /// Allocates the given amount of new entities and initializes them by their default values.
    ///
    /// Returns the index to the first entity allocated this way.
    /// Indices of allocated entities are guaranteed to be continuous.
    ///
    /// # Panics
    ///
    /// If the operation causes the entity arena to allocate more than or equal to `u32::MAX`
    /// entities in total.
    pub fn alloc_default(&mut self, amount: usize) -> Idx<T> {
        let raw_idx = self.max_key();
        let new_len = self.len() + amount;
        assert!(new_len < u32::MAX as usize);
        self.entities.resize_with(new_len, Default::default);
        Idx::from_raw(raw_idx)
    }
}

impl<T> EntityArena<T> {
    /// Returns the key for the next allocated entity.
    fn max_key(&self) -> RawIdx {
        RawIdx::from_u32(self.entities.len() as u32)
    }

    /// Allocates a new entity and returns a unique index to it.
    ///
    /// # Note
    ///
    /// The returned index can be used to query and mutate data of
    /// the entity and to add, remove or query associated components
    /// of it using secondary data structures.
    #[inline]
    pub fn alloc(&mut self, entity: T) -> Idx<T> {
        let raw_idx = self.max_key();
        self.entities.push(entity);
        Idx::from_raw(raw_idx)
    }

    /// Clears the entire entity arena.
    ///
    /// Removes all entities. Associated components must no longer be used.
    pub fn clear(&mut self) {
        self.entities.clear()
    }

    /// Reallocates the entity arena to make it take up as little space as possible.
    pub fn shrink_to_fit(&mut self) {
        self.entities.shrink_to_fit();
    }

    /// Returns the number of created entities.
    pub fn len(&self) -> usize {
        self.entities.len()
    }

    /// Returns `true` if no entities have yet been created.
    pub fn is_empty(&self) -> bool {
        self.entities.is_empty()
    }

    /// Converts a typed index into a `usize` to be used as slice or array index.
    fn idx_to_usize(index: Idx<T>) -> usize {
        index.into_raw().into_u32() as usize
    }

    /// Returns `true` if the entity at the index has been allocated.
    #[inline]
    pub fn contains_key(&self, index: Idx<T>) -> bool {
        index.into_raw() < self.max_key()
    }

    /// Returns a shared reference to the entity at the index if any.
    #[inline]
    pub fn get(&self, index: Idx<T>) -> Option<&T> {
        let index = Self::idx_to_usize(index);
        self.entities.get(index)
    }

    /// Returns an exclusive reference to the entity at the index if any.
    #[inline]
    pub fn get_mut(&mut self, index: Idx<T>) -> Option<&mut T> {
        let index = Self::idx_to_usize(index);
        self.entities.get_mut(index)
    }

    /// Returns an iterator over the indices of the stored entities.
    pub fn indices(&self) -> Indices<T> {
        Indices::new(RawIdx::from_u32(0), self.max_key())
    }

    /// Returns an iterator over shared references to the allocated entities of the entity arena.
    pub fn values(&self) -> Entities<T> {
        Entities::new(&self.entities)
    }

    /// Returns an iterator over mutable references to the allocated entities of the entity arena.
    pub fn values_mut(&mut self) -> EntitiesMut<T> {
        EntitiesMut::new(&mut self.entities)
    }

    /// Returns an iterator over the indices and shared references to their associated data.
    pub fn iter(&self) -> Iter<T> {
        Iter::new(RawIdx::from_u32(0), self.max_key(), &self.entities)
    }

    /// Returns an iterator over the indices and shared references to their associated data.
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut::new(RawIdx::from_u32(0), self.max_key(), &mut self.entities)
    }
}

impl<T> Index<Idx<T>> for EntityArena<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: Idx<T>) -> &Self::Output {
        let index = Self::idx_to_usize(index);
        &self.entities[index]
    }
}

impl<T> IndexMut<Idx<T>> for EntityArena<T> {
    #[inline]
    fn index_mut(&mut self, index: Idx<T>) -> &mut Self::Output {
        let index = Self::idx_to_usize(index);
        &mut self.entities[index]
    }
}

impl<T> FromIterator<T> for EntityArena<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        EntityArena {
            entities: Vec::from_iter(iter),
        }
    }
}

impl<'a, T> IntoIterator for &'a EntityArena<T> {
    type Item = (Idx<T>, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut EntityArena<T> {
    type Item = (Idx<T>, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
