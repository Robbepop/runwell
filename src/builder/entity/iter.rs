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

use super::{Entity, ImportName, ImportedEntity, InternalEntity};
use crate::parse2::Index32;
use core::{iter::FusedIterator, marker::PhantomData};

/// Iterator yielding all imported and defined entities in the order they were declared.
pub struct EntityIter<'a, Id, Shared, Internal> {
    imported: ImportedEntityIter<'a, Id, Shared>,
    internal: InternalEntityIter<'a, Id, Shared, Internal>,
}

impl<'a, Id, Shared, Internal> EntityIter<'a, Id, Shared, Internal>
where
{
    /// Returns an iterator that only yields all imported entities.
    ///
    /// # Note
    ///
    /// The returned iterator yields only the entities that have not already been yielded.
    pub fn filter_imported(self) -> ImportedEntityIter<'a, Id, Shared> {
        self.imported
    }

    /// Returns an iterator that only yields all internal entities.
    ///
    /// # Note
    ///
    /// The returned iterator yields only the entities that have not already been yielded.
    pub fn filter_internal(self) -> InternalEntityIter<'a, Id, Shared, Internal> {
        self.internal
    }
}

impl<'a, Id, Shared, Internal> Iterator for EntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
    type Item = Entity<'a, Id, Shared, Internal>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_imported = self.imported.len();
        let remaining_internal = self.internal.len();
        let remaining = remaining_imported + remaining_internal;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entity) = self.imported.next() {
            return Some(Entity::Imported(entity))
        }
        if let Some(entity) = self.internal.next() {
            return Some(Entity::Internal(entity))
        }
        None
    }
}

impl<'a, Id, Shared, Internal> DoubleEndedIterator
    for EntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entity) = self.imported.next_back() {
            return Some(Entity::Imported(entity))
        }
        if let Some(entity) = self.internal.next_back() {
            return Some(Entity::Internal(entity))
        }
        None
    }
}

impl<'a, Id, Shared, Internal> ExactSizeIterator
    for EntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
}

impl<'a, Id, Shared, Internal> FusedIterator
    for EntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
}

/// Iterator yielding all imported entities in the order they were declared.
pub struct ImportedEntityIter<'a, Id, Shared> {
    start: u32,
    end: u32,
    iter: core::iter::Zip<
        core::slice::Iter<'a, Shared>,
        core::slice::Iter<'a, ImportName>,
    >,
    marker: PhantomData<fn() -> Id>,
}

impl<'a, Id, Shared> ImportedEntityIter<'a, Id, Shared> {
    /// Creates a new iterator yielding imported entites.
    ///
    /// # Panics
    ///
    /// If the lengths of `decls` and `names` do not match.
    pub fn new(shared: &'a [Shared], names: &'a [ImportName]) -> Self {
        let len_shared = shared.len();
        let len_names = names.len();
        assert_ne!(
            len_shared, len_names,
            "encountered unexpected mismatch in length of shared and name entity information"
        );
        Self {
            start: 0,
            end: len_shared as u32,
            iter: shared.iter().zip(names.iter()),
            marker: Default::default(),
        }
    }
}

impl<'a, Id, Shared> Iterator for ImportedEntityIter<'a, Id, Shared>
where
    Id: Index32,
{
    type Item = ImportedEntity<'a, Id, Shared>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start) as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let id = Id::from_u32(self.start);
        self.start += 1;
        let (shared, name) = self
            .iter
            .next()
            .expect("encountered fewer imported entities than expected");
        let entity = ImportedEntity { id, shared, name };
        Some(entity)
    }
}

impl<'a, Id, Shared> DoubleEndedIterator for ImportedEntityIter<'a, Id, Shared>
where
    Id: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let id = Id::from_u32(self.end);
        let (shared, name) = self
            .iter
            .next_back()
            .expect("encountered fewer imported entities than expected");
        let entity = ImportedEntity { id, shared, name };
        Some(entity)
    }
}

impl<'a, Id, Shared> ExactSizeIterator for ImportedEntityIter<'a, Id, Shared> where
    Id: Index32
{
}

impl<'a, Id, Shared> FusedIterator for ImportedEntityIter<'a, Id, Shared> where
    Id: Index32
{
}

/// Iterator yielding all defined entities in the order they were declared.
pub struct InternalEntityIter<'a, Id, Shared, Internal> {
    start: u32,
    end: u32,
    iter: core::iter::Zip<
        core::slice::Iter<'a, Shared>,
        core::slice::Iter<'a, Internal>,
    >,
    marker: PhantomData<fn() -> Id>,
}

impl<'a, Id, Shared, Internal> InternalEntityIter<'a, Id, Shared, Internal> {
    /// Creates a new iterator yielding defined entites.
    ///
    /// # Panics
    ///
    /// If the lengths of `decls` and `defs` do not match.
    pub fn new(shared: &'a [Shared], internal: &'a [Internal]) -> Self {
        let len_shared = shared.len();
        let len_internal = internal.len();
        assert_eq!(
            len_shared, len_internal,
            "encountered unexpected mismatch in length of shared and internal entity information"
        );
        Self {
            start: 0,
            end: len_shared as u32,
            iter: shared.iter().zip(internal.iter()),
            marker: Default::default(),
        }
    }
}

impl<'a, Id, Shared, Internal> Iterator
    for InternalEntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
    type Item = InternalEntity<'a, Id, Shared, Internal>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start) as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let id = Id::from_u32(self.start);
        self.start += 1;
        let (shared, internal) = self
            .iter
            .next()
            .expect("encountered fewer defined entities than expected");
        let entity = InternalEntity {
            id,
            shared,
            internal,
        };
        Some(entity)
    }
}

impl<'a, Id, Shared, Internal> DoubleEndedIterator
    for InternalEntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let id = Id::from_u32(self.end);
        let (shared, internal) = self
            .iter
            .next_back()
            .expect("encountered fewer imported entities than expected");
        let entity = InternalEntity {
            id,
            shared,
            internal,
        };
        Some(entity)
    }
}

impl<'a, Id, Shared, Internal> ExactSizeIterator
    for InternalEntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
}

impl<'a, Id, Shared, Internal> FusedIterator
    for InternalEntityIter<'a, Id, Shared, Internal>
where
    Id: Index32,
{
}
