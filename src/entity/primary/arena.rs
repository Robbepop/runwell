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

use super::iter::{Indices, Iter, IterMut, Entities, EntitiesMut};
use crate::entity::{Idx, RawIdx};
use core::ops::{Index, IndexMut};

/// Primary map to create new entities and store required data for them.
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

impl<T> EntityArena<T> {
    /// Returns the key for the next allocated entity.
    fn max_key(&self) -> RawIdx {
        RawIdx::from_u32(self.entities.len() as u32)
    }

    /// Creates a new entity and returns a unique key to it.
    ///
    /// # Note
    ///
    /// The key can be used to query and mutate data of the entity
    /// and to add, remove or query the components of it using
    /// secondary data structures.
    pub fn create(&mut self, entity: T) -> Idx<T> {
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

    /// Returns the number of created entities.
    pub fn len(&self) -> usize {
        self.entities.len()
    }

    /// Returns `true` if no entities have yet been created.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a shared reference to the entity at the index if any.
    pub fn get(&self, index: Idx<T>) -> Option<&T> {
        self.entities.get(index.into_raw().into_u32() as usize)
    }

    /// Returns an exclusive reference to the entity at the index if any.
    pub fn get_mut(&mut self, index: Idx<T>) -> Option<&mut T> {
        self.entities.get_mut(index.into_raw().into_u32() as usize)
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

    fn index(&self, index: Idx<T>) -> &Self::Output {
        self.get(index).expect("invalid index for entitiy")
    }
}

impl<T> IndexMut<Idx<T>> for EntityArena<T> {
    fn index_mut(&mut self, index: Idx<T>) -> &mut Self::Output {
        self.get_mut(index).expect("invalid key for entity")
    }
}
