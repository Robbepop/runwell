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

use super::ImportName;

/// A shared reference to either an imported or internal entity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Entity<'a, Id, Shared, Internal> {
    Imported(ImportedEntity<'a, Id, Shared>),
    Internal(InternalEntity<'a, Id, Shared, Internal>),
}

impl<'a, Id, Shared, Internal> Entity<'a, Id, Shared, Internal>
where
    Id: Copy,
{
    /// Returns the unique ID of the entity.
    pub fn id(&self) -> Id {
        match self {
            Self::Imported(imported_entity) => imported_entity.id,
            Self::Internal(defined_entity) => defined_entity.id,
        }
    }
}

impl<'a, Id, Shared, Internal> Entity<'a, Id, Shared, Internal> {
    /// Returns the data of the entity that is shared between imported and internal entities.
    pub fn shared(&self) -> &'a Shared {
        match self {
            Self::Imported(imported_entity) => &imported_entity.shared,
            Self::Internal(internal_entity) => &internal_entity.shared,
        }
    }

    /// Returns the entity if it represents an imported entity, otherwise `None`.
    pub fn filter_map_imported(self) -> Option<ImportedEntity<'a, Id, Shared>> {
        if let Self::Imported(imported_entity) = self {
            return Some(imported_entity)
        }
        None
    }

    /// Returns the entity if it represents an imported entity, otherwise `None`.
    pub fn filter_map_internal(
        self,
    ) -> Option<InternalEntity<'a, Id, Shared, Internal>> {
        if let Self::Internal(internal_entity) = self {
            return Some(internal_entity)
        }
        None
    }

    /// Returns `true` if the entity is imported.
    pub fn is_imported(&self) -> bool {
        matches!(self, Self::Imported(_))
    }

    /// Returns `true` if the entity is internal.
    pub fn is_internal(&self) -> bool {
        matches!(self, Self::Internal(_))
    }
}

/// A reference to an imported entity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ImportedEntity<'a, Id, Shared> {
    /// The unique ID of the imported entity.
    pub id: Id,
    /// The data of the imported entity that it shares with internal entities.
    pub shared: &'a Shared,
    /// The import name of the imported entity.
    pub name: &'a ImportName,
}

/// A reference to an internal entity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct InternalEntity<'a, Id, Shared, Internal> {
    /// The unique ID of the internal entity.
    pub id: Id,
    /// The data of the imported entity that it shares with internal entities.
    pub shared: &'a Shared,
    /// The data that only internal entities have.
    pub internal: &'a Internal,
}

/// A mutable reference to either an imported or internal entity.
#[derive(Debug, PartialEq, Eq)]
pub enum EntityMut<'a, Id, Shared, Internal> {
    Imported(ImportedEntityMut<'a, Id, Shared>),
    Internal(InternalEntityMut<'a, Id, Shared, Internal>),
}

impl<'a, Id, Shared, Internal> EntityMut<'a, Id, Shared, Internal>
where
    Id: Copy,
{
    /// Returns the unique ID of the entity.
    pub fn id(&self) -> Id {
        match self {
            Self::Imported(imported_entity) => imported_entity.id,
            Self::Internal(defined_entity) => defined_entity.id,
        }
    }
}

impl<'a, Id, Shared, Internal> EntityMut<'a, Id, Shared, Internal> {
    /// Returns the declaration of the entity.
    pub fn shared(self) -> &'a mut Shared {
        match self {
            Self::Imported(imported_entity) => imported_entity.shared,
            Self::Internal(defined_entity) => defined_entity.shared,
        }
    }

    /// Returns the entity if it represents an imported entity, otherwise `None`.
    pub fn filter_map_imported(
        self,
    ) -> Option<ImportedEntityMut<'a, Id, Shared>> {
        if let Self::Imported(imported_entity) = self {
            return Some(imported_entity)
        }
        None
    }

    /// Returns the entity if it represents an internal entity, otherwise `None`.
    pub fn filter_map_internal(
        self,
    ) -> Option<InternalEntityMut<'a, Id, Shared, Internal>> {
        if let Self::Internal(internal_entity) = self {
            return Some(internal_entity)
        }
        None
    }

    /// Returns `true` if the entity is imported.
    pub fn is_imported(&self) -> bool {
        matches!(self, Self::Imported(_))
    }

    /// Returns `true` if the entity is defined.
    pub fn is_defined(&self) -> bool {
        matches!(self, Self::Internal(_))
    }
}

/// A mutable reference to an imported entity.
#[derive(Debug, PartialEq, Eq)]
pub struct ImportedEntityMut<'a, Id, Shared> {
    /// The unique ID of the imported entity.
    pub id: Id,
    /// The data of the imported entity that it shares with internal entities.
    pub shared: &'a mut Shared,
    /// The import name of the imported entity.
    pub name: &'a mut ImportName,
}

/// A mutable reference to an internal entity.
#[derive(Debug, PartialEq, Eq)]
pub struct InternalEntityMut<'a, Id, Shared, Internal> {
    /// The unique ID of the internal entity.
    pub id: Id,
    /// The data of the imported entity that it shares with internal entities.
    pub shared: &'a mut Shared,
    /// The definition of the internal entity.
    pub internal: &'a mut Internal,
}
