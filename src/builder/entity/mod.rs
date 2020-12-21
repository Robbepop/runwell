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

//! Provides data structures to store entities similar to an entity component architecture.
//!
//! It is simplified and optimized to work with imported and internal entities
//! where both share some common data, imported entities have an import name and internal
//! entities have some additional generic data that is associated to them.

mod error;
mod iter;
mod output;

pub use self::{
    error::EntityError,
    iter::{EntityIter, ImportedEntityIter, InternalEntityIter},
    output::{
        Entity,
        EntityMut,
        ImportedEntity,
        ImportedEntityMut,
        InternalEntity,
        InternalEntityMut,
    },
};

use super::{BuildError, ImportName};
use crate::parse2::Index32;
use core::marker::PhantomData;

/// Data structure holding entities identified by `Id`.
///
/// # Note
///
/// Entities can either be imported or internal. Imported entities have
/// an import name whereas internal entities may hold additional data
/// of type `Internal`.
///
/// Both, imported and internal entities have `Shared` data associated to them.
#[derive(Debug)]
pub struct Entities<Id, Shared, Internal> {
    /// The number of imported entities.
    len_imported: usize,
    /// The amount of reserved internal entities if already set.
    reserved_internals: Option<usize>,
    /// Data associated to imported and internal entities.
    shared: Vec<Shared>,
    /// The import names of the imported entities.
    imported: Vec<ImportName>,
    /// The definitions of the defined entities.
    internal: Vec<Internal>,
    /// Silences the Rust compiler warnings for unused `Id` type.
    id_marker: PhantomData<fn() -> Id>,
}

impl<Id, Shared, Internal> Default for Entities<Id, Shared, Internal> {
    fn default() -> Self {
        Self {
            len_imported: 0,
            reserved_internals: None,
            shared: Vec::new(),
            imported: Vec::new(),
            internal: Vec::new(),
            id_marker: Default::default(),
        }
    }
}

impl<Id, Shared, Internal> Entities<Id, Shared, Internal> {
    /// Returns the number of imported and internal entities.
    pub fn len_entities(&self) -> usize {
        self.internal.len()
    }

    /// Returns the number of imported entities.
    pub fn len_imported(&self) -> usize {
        self.len_imported
    }

    /// Returns the number of internal entities.
    pub fn len_internal(&self) -> usize {
        self.len_entities() - self.len_imported()
    }

    /// Returns `true` if there are imported entities.
    fn has_imported_entities(&self) -> bool {
        !self.imported.is_empty()
    }

    /// Returns `true` if there are internal entities.
    fn has_internal_entities(&self) -> bool {
        !self.internal.is_empty()
    }

    /// Reserve space for the given number of internal entities.
    ///
    /// # Errors
    ///
    /// If a reservation has already been made.
    pub fn reserve_internals(
        &mut self,
        additional: usize,
    ) -> Result<(), BuildError> {
        if let Some(previous_reservation) = self.reserved_internals {
            return Err(EntityError::DuplicateReservedInternals {
                previous_reservation,
                actual_reservation: additional,
            })
            .map_err(Into::into)
        }
        self.shared.reserve(additional);
        self.internal.reserve(additional);
        Ok(())
    }
}

impl<Id, Shared, Internal> Entities<Id, Shared, Internal>
where
    Id: Index32,
{
    /// Pushes a new internal entity.
    ///
    /// # Errors
    ///
    /// If more entities have been pushed than reserved via [`Self::reserve_internals`].
    pub fn push_internal(
        &mut self,
        shared: Shared,
        internal: Internal,
    ) -> Result<Id, BuildError> {
        if let Some(reserved_internals) = self.reserved_internals {
            if self.internal.len() == reserved_internals {
                return Err(EntityError::TooManyDefinitions {
                    reserved: reserved_internals,
                })
                .map_err(Into::into)
            }
        }
        let id = Id::from_u32(self.len_entities() as u32);
        self.shared.push(shared);
        self.internal.push(internal);
        Ok(id)
    }

    /// Pushes a new imported entitiy.
    ///
    /// # Errors
    ///
    /// Returns an error if defined entities have already been pushed before.
    pub fn push_imported(
        &mut self,
        name: ImportName,
        shared: Shared,
    ) -> Result<Id, BuildError> {
        if self.has_internal_entities() {
            return Err(EntityError::PushImportAfterInternals {
                count_internal: self.len_internal(),
            })
            .map_err(Into::into)
        }
        let id = Id::from_u32(self.len_entities() as u32);
        self.shared.push(shared);
        self.imported.push(name);
        self.len_imported += 1;
        Ok(id)
    }

    /// Returns `true` if `id` refers to an imported entity.
    pub fn is_imported_entity(&self, id: Id) -> bool {
        (id.into_u32() as usize) < self.len_imported()
    }

    /// Returns `true` if `id` refers to an internal entity.
    pub fn is_interal_entity(&self, id: Id) -> bool {
        !self.is_imported_entity(id)
    }

    /// Returns a shared reference to the entity associated with the given ID if any.
    ///
    /// Returns either an [`ImportedEntity`] or a [`InternalEntity`].
    /// Returns `None` if the ID is out of bounds.
    pub fn get(&self, id: Id) -> Option<Entity<Id, Shared, Internal>> {
        let id_size = id.into_u32() as usize;
        if id_size >= self.len_entities() {
            return None
        }
        let entity = match self.is_imported_entity(id) {
            true => {
                Entity::Imported(ImportedEntity {
                    id,
                    shared: &self.shared[id_size],
                    name: &self.imported[id_size],
                })
            }
            false => {
                Entity::Internal(InternalEntity {
                    id,
                    shared: &self.shared[id_size],
                    internal: &self.internal[id_size],
                })
            }
        };
        Some(entity)
    }

    /// Returns a mutable reference to the entity associated with the given ID if any.
    ///
    /// Returns either an [`ImportedEntityMut`] or a [`InternalEntityMut`].
    /// Returns `None` if the ID is out of bounds.
    pub fn get_mut(
        &mut self,
        id: Id,
    ) -> Option<EntityMut<Id, Shared, Internal>> {
        let id_size = id.into_u32() as usize;
        if id_size >= self.len_entities() {
            return None
        }
        let entity = match self.is_imported_entity(id) {
            true => {
                EntityMut::Imported(ImportedEntityMut {
                    id,
                    shared: &mut self.shared[id_size],
                    name: &mut self.imported[id_size],
                })
            }
            false => {
                EntityMut::Internal(InternalEntityMut {
                    id,
                    shared: &mut self.shared[id_size],
                    internal: &mut self.internal[id_size],
                })
            }
        };
        Some(entity)
    }
}
