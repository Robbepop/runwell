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

use super::iter::Indices;
use crate::{Idx, RawIdx};
use core::marker::PhantomData;

/// Primary map to create new entities without the need to directly store data with them.
///
/// # Note
///
/// - Use this if your entities are zero-sized types and all their associated component
///   data lives in component data structures.
/// - The memory footprint of this data structure is just a single unsigned integer (`u32`),
///   so this arena type is just a glorified counter.
///
/// For efficiency and safety reasons it is not possible to remove entities.
#[derive(Debug)]
pub struct PhantomEntityArena<T> {
    current: u32,
    marker: PhantomData<fn() -> T>,
}

impl<T> Clone for PhantomEntityArena<T> {
    fn clone(&self) -> Self {
        Self {
            current: self.current,
            marker: Default::default(),
        }
    }
}

impl<T> Default for PhantomEntityArena<T> {
    fn default() -> Self {
        Self {
            current: 0,
            marker: Default::default(),
        }
    }
}

impl<T> PhantomEntityArena<T> {
    /// Returns the key for the next allocated entity.
    fn next_key(&self) -> RawIdx {
        RawIdx::from_u32(self.current)
    }

    /// Allocates some `amount` of new entities returning the index to the first.
    ///
    /// # Panics
    ///
    /// If the operation causes the entity arena to allocate more than or equal to `u32::MAX`
    /// entities in total.
    pub fn alloc_some(&mut self, amount: u32) -> Idx<T> {
        let key = self.next_key();
        self.current = self.current.checked_add(amount).unwrap_or_else(|| panic!(
            "overflowed the phantom arena with an amount of {} while being at {} already",
            amount,
            self.current,
        ));
        Idx::from_raw(key)
    }

    /// Clears the entire entity arena.
    ///
    /// Associated components must no longer be used.
    pub fn clear(&mut self) {
        self.current = 0;
    }

    /// Returns the number of created entities.
    pub fn len(&self) -> usize {
        self.current as usize
    }

    /// Returns `true` if no entities have yet been created.
    pub fn is_empty(&self) -> bool {
        self.current == 0
    }

    /// Returns `true` if the entity at the index has been allocated.
    #[inline]
    pub fn contains_key(&self, index: Idx<T>) -> bool {
        index.into_raw() < self.next_key()
    }

    /// Returns an iterator over the indices of the stored entities.
    pub fn indices(&self) -> Indices<T> {
        Indices::new(RawIdx::from_u32(0), self.next_key())
    }
}
