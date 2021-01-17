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

use super::iter::{Iter, IterMut, Keys};
use crate::Index32;
use core::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

/// Primary map to create new entities and store required data for them.
///
/// For efficiency and satety reasons it is not possible to remove entities.
#[derive(Debug)]
pub struct EntityArena<K, V> {
    entities: Vec<V>,
    key: PhantomData<fn() -> K>,
}

impl<K, V> Clone for EntityArena<K, V>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            entities: self.entities.clone(),
            key: Default::default(),
        }
    }
}

impl<K, V> Default for EntityArena<K, V> {
    fn default() -> Self {
        Self {
            entities: Default::default(),
            key: Default::default(),
        }
    }
}

impl<K, V> EntityArena<K, V>
where
    K: Index32,
{
    /// Returns the key for the next allocated entity.
    fn max_key(&self) -> K {
        K::from_u32(self.entities.len() as u32)
    }

    /// Creates a new entity and returns a unique key to it.
    ///
    /// # Note
    ///
    /// The key can be used to query and mutate data of the entity
    /// and to add, remove or query the components of it using
    /// secondary data structures.
    pub fn create(&mut self, entity: V) -> K {
        let id = self.max_key();
        self.entities.push(entity);
        id
    }

    /// Returns the number of created entities.
    pub fn len(&self) -> usize {
        self.entities.len()
    }

    /// Returns `true` if no entities have yet been created.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a shared reference to the entity at the key if any.
    pub fn get(&self, key: K) -> Option<&V> {
        self.entities.get(key.into_u32() as usize)
    }

    /// Returns an exclusive reference to the entity at the key if any.
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.entities.get_mut(key.into_u32() as usize)
    }

    /// Returns an iterator over the keys of the stored entities.
    pub fn keys(&self) -> Keys<K> {
        Keys::new(K::from_u32(0), self.max_key())
    }

    /// Returns an iterator over the keys and shared references to their associated data.
    pub fn iter(&self) -> Iter<K, V> {
        Iter::new(&self.entities)
    }

    /// Returns an iterator over the keys and shared references to their associated data.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut::new(&mut self.entities)
    }
}

impl<K, V> Index<K> for EntityArena<K, V>
where
    K: Index32,
{
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        self.get(index).expect("invalid key for entitiy")
    }
}

impl<K, V> IndexMut<K> for EntityArena<K, V>
where
    K: Index32,
{
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.get_mut(index).expect("invalid key for entity")
    }
}