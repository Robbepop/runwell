use crate::parse::{Index32, ParseError};
use core::{iter::FusedIterator, marker::PhantomData};
use derive_more::Display;

#[derive(Debug, Display, PartialEq, Eq)]
pub enum ModuleError {
    #[display(
        fmt = "encountered a new import after already containing definitions"
    )]
    PushImportAfterDefinitions,
    #[display(fmt = "encountered more definitions than have been expected")]
    TooManyDefinitions,
    #[display(fmt = "encountered duplicate reservations for definitions")]
    DuplicateReservedDefinitions,
    #[display(fmt = "some declarations are still missing their definitions")]
    MissingDefinitions,
}

/// A module and field name for an imported entity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportName {
    module_name: String,
    field_name: String,
}

impl ImportName {
    /// Creates a new import name from the given module and field names.
    pub fn new(module_name: &str, field_name: &str) -> Self {
        Self {
            module_name: module_name.to_string(),
            field_name: field_name.to_string(),
        }
    }

    /// Returns the module name of the import.
    pub fn module_name(&self) -> &str {
        &self.module_name
    }

    /// Returns the field name of the import.
    pub fn field_name(&self) -> &str {
        &self.field_name
    }
}

/// Holds imported and defined Wasm entities.
#[derive(Debug)]
pub struct ImportedOrDefined<Id, Decl, Def> {
    /// The number of imported entities.
    len_imported: usize,
    /// Declarations of important and defined entities.
    declarations: Vec<Decl>,
    /// The definitions of the defined entities.
    definitions: Vec<Def>,
    /// The import names of the imported entities.
    namespaces: Vec<ImportName>,
    /// Silences the Rust compiler warnings for unused `Id` type.
    id_marker: PhantomData<fn() -> Id>,
    /// The amount of expected definitions if already set.
    expected_definitions: Option<usize>,
}

impl<Id, Decl, Def> Default for ImportedOrDefined<Id, Decl, Def> {
    fn default() -> Self {
        Self {
            len_imported: 0,
            declarations: Vec::new(),
            definitions: Vec::new(),
            namespaces: Vec::new(),
            id_marker: Default::default(),
            expected_definitions: None,
        }
    }
}

impl<Id, Decl, Def> ImportedOrDefined<Id, Decl, Def> {
    /// Returns the number of imported and defined entities.
    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Returns the number of imported entities.
    pub fn len_imported(&self) -> usize {
        self.len_imported
    }

    /// Returns the number of defined entities.
    pub fn len_defined(&self) -> usize {
        self.len() - self.len_imported()
    }

    /// Reserve space for the given number of expected definitions.
    pub fn reserve_definitions(
        &mut self,
        additional: usize,
    ) -> Result<(), ParseError> {
        if let Some(_expected_definitions) = self.expected_definitions {
            return Err(ModuleError::DuplicateReservedDefinitions)
                .map_err(Into::into)
        }
        self.declarations.reserve(additional);
        self.definitions.reserve(additional);
        Ok(())
    }

    /// Returns `true` if there are defined entities.
    fn has_definitions(&self) -> bool {
        !self.definitions.is_empty()
    }
}

impl<Id, Decl, Def> ImportedOrDefined<Id, Decl, Def>
where
    Id: Index32,
{
    /// Pushes a new defined entity.
    ///
    /// # Errors
    ///
    /// If we pushed more definitions than expected by [`Self::reserve_definitions`].
    pub fn push_defined(
        &mut self,
        declaration: Decl,
        definition: Def,
    ) -> Result<Id, ParseError> {
        if let Some(expected_definitions) = self.expected_definitions {
            if self.definitions.len() == expected_definitions {
                return Err(ModuleError::TooManyDefinitions).map_err(Into::into)
            }
        }
        let id = Id::from_u32(self.len() as u32);
        self.declarations.push(declaration);
        self.definitions.push(definition);
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
        declaration: Decl,
    ) -> Result<Id, ParseError> {
        if self.has_definitions() {
            return Err(ModuleError::PushImportAfterDefinitions)
                .map_err(Into::into)
        }
        let id = Id::from_u32(self.len() as u32);
        self.declarations.push(declaration);
        self.namespaces.push(name);
        self.len_imported += 1;
        Ok(id)
    }

    /// Returns `true` if `id` refers to an imported entity.
    pub fn is_imported(&self, id: Id) -> bool {
        (id.into_u32() as usize) < self.len_imported()
    }

    /// Returns `true` if `id` refers to a defined entity.
    pub fn is_defined(&self, id: Id) -> bool {
        !self.is_imported(id)
    }

    /// Returns the entity associated with the given ID if any.
    ///
    /// Returns either an [`ImportedEntity`] or a [`DefinedEntity`].
    /// Returns `None` if the ID is out of bounds.
    pub fn get(&self, id: Id) -> Option<Entity<Id, Decl, Def>> {
        let id_size = id.into_u32() as usize;
        if id_size >= self.len() {
            return None
        }
        let entity = match self.is_imported(id) {
            true => {
                Entity::Imported(ImportedEntity {
                    id,
                    name: &self.namespaces[id_size],
                    decl: &self.declarations[id_size],
                })
            }
            false => {
                Entity::Defined(DefinedEntity {
                    id,
                    decl: &self.declarations[id_size],
                    def: &self.definitions[id_size],
                })
            }
        };
        Some(entity)
    }

    /// Returns the imported entity associated with the given ID if any.
    ///
    /// Returns `None` if the ID refers to a defined entity.
    pub fn get_imported(
        &self,
        id: Id,
    ) -> Option<ImportedEntity<Id, Decl>> {
        if let Entity::Imported(imported_entity) = self.get(id)? {
            return Some(imported_entity)
        }
        None
    }

    /// Returns the defined entity associated with the given ID if any.
    ///
    /// Returns `None` if the ID refers to an imported entity.
    pub fn get_defined(
        &self,
        id: Id,
    ) -> Option<DefinedEntity<Id, Decl, Def>> {
        if let Entity::Defined(defined_entity) = self.get(id)? {
            return Some(defined_entity)
        }
        None
    }

    /// Returns a mutable reference to the entity associated with the given ID if any.
    ///
    /// Returns either an [`ImportedEntity`] or a [`DefinedEntity`].
    /// Returns `None` if the ID is out of bounds.
    pub fn get_mut(
        &mut self,
        id: Id,
    ) -> Option<EntityMut<Id, Decl, Def>> {
        let id_size = id.into_u32() as usize;
        if id_size >= self.len() {
            return None
        }
        let entity = match self.is_imported(id) {
            true => {
                EntityMut::Imported(ImportedEntityMut {
                    id,
                    name: &mut self.namespaces[id_size],
                    decl: &mut self.declarations[id_size],
                })
            }
            false => {
                EntityMut::Defined(DefinedEntityMut {
                    id,
                    decl: &mut self.declarations[id_size],
                    def: &mut self.definitions[id_size],
                })
            }
        };
        Some(entity)
    }

    /// Returns a mutable reference to the imported entity associated with the given ID if any.
    ///
    /// Returns `None` if the ID refers to a defined entity.
    pub fn get_imported_mut(
        &mut self,
        id: Id,
    ) -> Option<ImportedEntityMut<Id, Decl>> {
        if let EntityMut::Imported(imported_entity) = self.get_mut(id)? {
            return Some(imported_entity)
        }
        None
    }

    /// Returns a mutable reference to the defined entity associated with the given ID if any.
    ///
    /// Returns `None` if the ID refers to an imported entity.
    pub fn get_defined_mut(
        &mut self,
        id: Id,
    ) -> Option<DefinedEntityMut<Id, Decl, Def>> {
        if let EntityMut::Defined(defined_entity) = self.get_mut(id)? {
            return Some(defined_entity)
        }
        None
    }

    /// Returns `true` if definitions for some declarations are still missing.
    ///
    /// Returns `false` if no reservation for definitions have yet taken place.
    fn is_missing_definitions(&self) -> bool {
        if let Some(expected) = self.expected_definitions {
            if self.len_defined() != expected {
                return true
            }
        }
        false
    }

    /// Returns an iterator yielding all imported or defined entities.
    ///
    /// # Errors
    ///
    /// If there are missing definitions for declared entities.
    pub fn iter(&self) -> Result<EntityIter<Id, Decl, Def>, ParseError> {
        let imported = self.iter_imported()?;
        let defined = self.iter_defined()?;
        Ok(EntityIter { imported, defined })
    }

    /// Returns an iterator yielding all imported entities.
    ///
    /// # Errors
    ///
    /// If there are missing definitions for declared entities.
    pub fn iter_imported(
        &self,
    ) -> Result<ImportedEntityIter<Id, Decl>, ParseError> {
        if self.is_missing_definitions() {
            return Err(ModuleError::MissingDefinitions).map_err(Into::into)
        }
        let len_imported = self.len_imported();
        assert_eq!(self.namespaces.len(), len_imported);
        Ok(ImportedEntityIter::new(
            &self.declarations[..len_imported],
            &self.namespaces[..],
        ))
    }

    /// Returns an iterator yielding all defined entities.
    ///
    /// # Errors
    ///
    /// If there are missing definitions for declared entities.
    pub fn iter_defined(
        &self,
    ) -> Result<DefinedEntityIter<Id, Decl, Def>, ParseError> {
        if self.is_missing_definitions() {
            return Err(ModuleError::MissingDefinitions).map_err(Into::into)
        }
        let len_imported = self.len_imported();
        let len_defined = self.len_defined();
        assert_eq!(self.definitions.len(), len_defined);
        Ok(DefinedEntityIter::new(
            &self.declarations[len_imported..(len_imported + len_defined)],
            &self.definitions[..len_defined],
        ))
    }
}

/// Iterator yielding all imported and defined entities in the order they were declared.
pub struct EntityIter<'a, Id, Decl, Def> {
    imported: ImportedEntityIter<'a, Id, Decl>,
    defined: DefinedEntityIter<'a, Id, Decl, Def>,
}

impl<'a, Id, Decl, Def> Iterator for EntityIter<'a, Id, Decl, Def>
where
    Id: Index32,
{
    type Item = Entity<'a, Id, Decl, Def>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_imported = self.imported.len();
        let remaining_defined = self.defined.len();
        let remaining = remaining_imported + remaining_defined;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entity) = self.imported.next() {
            return Some(Entity::Imported(entity))
        }
        if let Some(entity) = self.defined.next() {
            return Some(Entity::Defined(entity))
        }
        None
    }
}

impl<'a, Id, Decl, Def> DoubleEndedIterator for EntityIter<'a, Id, Decl, Def>
where
    Id: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entity) = self.imported.next_back() {
            return Some(Entity::Imported(entity))
        }
        if let Some(entity) = self.defined.next_back() {
            return Some(Entity::Defined(entity))
        }
        None
    }
}

impl<'a, Id, Decl, Def> ExactSizeIterator for EntityIter<'a, Id, Decl, Def> where
    Id: Index32
{
}

impl<'a, Id, Decl, Def> FusedIterator for EntityIter<'a, Id, Decl, Def> where
    Id: Index32
{
}

/// Iterator yielding all imported entities in the order they were declared.
pub struct ImportedEntityIter<'a, Id, Decl> {
    start: u32,
    end: u32,
    iter: core::iter::Zip<
        core::slice::Iter<'a, Decl>,
        core::slice::Iter<'a, ImportName>,
    >,
    marker: PhantomData<fn() -> Id>,
}

impl<'a, Id, Decl> ImportedEntityIter<'a, Id, Decl> {
    /// Creates a new iterator yielding imported entites.
    ///
    /// # Panics
    ///
    /// If the lengths of `decls` and `names` do not match.
    pub fn new(decls: &'a [Decl], names: &'a [ImportName]) -> Self {
        let len_decls = decls.len();
        let len_names = names.len();
        assert_ne!(
            len_decls, len_names,
            "encountered mismatch in length of decls and import names"
        );
        Self {
            start: 0,
            end: len_decls as u32,
            iter: decls.iter().zip(names.iter()),
            marker: Default::default(),
        }
    }
}

impl<'a, Id, Decl> Iterator for ImportedEntityIter<'a, Id, Decl>
where
    Id: Index32,
{
    type Item = ImportedEntity<'a, Id, Decl>;

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
        let (decl, name) = self
            .iter
            .next()
            .expect("encountered fewer imported entities than expected");
        let entity = ImportedEntity { id, decl, name };
        Some(entity)
    }
}

impl<'a, Id, Decl> DoubleEndedIterator for ImportedEntityIter<'a, Id, Decl>
where
    Id: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let id = Id::from_u32(self.end);
        let (decl, name) = self
            .iter
            .next_back()
            .expect("encountered fewer imported entities than expected");
        let entity = ImportedEntity { id, decl, name };
        Some(entity)
    }
}

impl<'a, Id, Decl> ExactSizeIterator for ImportedEntityIter<'a, Id, Decl> where
    Id: Index32
{
}

impl<'a, Id, Decl> FusedIterator for ImportedEntityIter<'a, Id, Decl> where
    Id: Index32
{
}

/// Iterator yielding all defined entities in the order they were declared.
pub struct DefinedEntityIter<'a, Id, Decl, Def> {
    start: u32,
    end: u32,
    iter: core::iter::Zip<
        core::slice::Iter<'a, Decl>,
        core::slice::Iter<'a, Def>,
    >,
    marker: PhantomData<fn() -> Id>,
}

impl<'a, Id, Decl, Def> DefinedEntityIter<'a, Id, Decl, Def> {
    /// Creates a new iterator yielding defined entites.
    ///
    /// # Panics
    ///
    /// If the lengths of `decls` and `defs` do not match.
    pub fn new(decls: &'a [Decl], defs: &'a [Def]) -> Self {
        let len_decls = decls.len();
        let len_defs = defs.len();
        assert_ne!(
            len_decls, len_defs,
            "encountered mismatch in length of declarations and definitions"
        );
        Self {
            start: 0,
            end: len_decls as u32,
            iter: decls.iter().zip(defs.iter()),
            marker: Default::default(),
        }
    }
}

impl<'a, Id, Decl, Def> Iterator for DefinedEntityIter<'a, Id, Decl, Def>
where
    Id: Index32,
{
    type Item = DefinedEntity<'a, Id, Decl, Def>;

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
        let (decl, def) = self
            .iter
            .next()
            .expect("encountered fewer defined entities than expected");
        let entity = DefinedEntity { id, decl, def };
        Some(entity)
    }
}

impl<'a, Id, Decl, Def> DoubleEndedIterator
    for DefinedEntityIter<'a, Id, Decl, Def>
where
    Id: Index32,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let id = Id::from_u32(self.end);
        let (decl, def) = self
            .iter
            .next_back()
            .expect("encountered fewer imported entities than expected");
        let entity = DefinedEntity { id, decl, def };
        Some(entity)
    }
}

impl<'a, Id, Decl, Def> ExactSizeIterator
    for DefinedEntityIter<'a, Id, Decl, Def>
where
    Id: Index32,
{
}

impl<'a, Id, Decl, Def> FusedIterator for DefinedEntityIter<'a, Id, Decl, Def> where
    Id: Index32
{
}

/// A reference to either an imported or defined entity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Entity<'a, Id, Decl, Def> {
    Imported(ImportedEntity<'a, Id, Decl>),
    Defined(DefinedEntity<'a, Id, Decl, Def>),
}

impl<'a, Id, Decl, Def> Entity<'a, Id, Decl, Def>
where
    Id: Copy,
{
    /// Returns the unique ID of the entity.
    pub fn id(&self) -> Id {
        match self {
            Self::Imported(imported_entity) => imported_entity.id,
            Self::Defined(defined_entity) => defined_entity.id,
        }
    }
}

impl<'a, Id, Decl, Def> Entity<'a, Id, Decl, Def> {
    /// Returns the declaration of the entity.
    pub fn decl(&self) -> &'a Decl {
        match self {
            Self::Imported(imported_entity) => &imported_entity.decl,
            Self::Defined(defined_entity) => &defined_entity.decl,
        }
    }

    /// Returns `true` if the entity is imported.
    pub fn is_imported(&self) -> bool {
        matches!(self, Self::Imported(_))
    }

    /// Returns `true` if the entity is defined.
    pub fn is_defined(&self) -> bool {
        matches!(self, Self::Defined(_))
    }
}

/// A reference to an imported entity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ImportedEntity<'a, Id, Decl> {
    /// The unique ID of the imported entity.
    pub id: Id,
    /// The import name of the imported entity.
    pub name: &'a ImportName,
    /// The declaration of the imported entity.
    pub decl: &'a Decl,
}

/// A reference to a defined entity.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct DefinedEntity<'a, Id, Decl, Def> {
    /// The unique ID of the imported entity.
    pub id: Id,
    /// The declaration of the defined entity.
    pub decl: &'a Decl,
    /// The definition of the defined entity.
    pub def: &'a Def,
}

/// A mutable reference to either an imported or defined entity.
#[derive(Debug, PartialEq, Eq)]
pub enum EntityMut<'a, Id, Decl, Def> {
    Imported(ImportedEntityMut<'a, Id, Decl>),
    Defined(DefinedEntityMut<'a, Id, Decl, Def>),
}

impl<'a, Id, Decl, Def> EntityMut<'a, Id, Decl, Def>
where
    Id: Copy,
{
    /// Returns the unique ID of the entity.
    pub fn id(&self) -> Id {
        match self {
            Self::Imported(imported_entity) => imported_entity.id,
            Self::Defined(defined_entity) => defined_entity.id,
        }
    }
}

impl<'a, Id, Decl, Def> EntityMut<'a, Id, Decl, Def> {
    /// Returns the declaration of the entity.
    pub fn decl(self) -> &'a mut Decl {
        match self {
            Self::Imported(imported_entity) => imported_entity.decl,
            Self::Defined(defined_entity) => defined_entity.decl,
        }
    }

    /// Returns `true` if the entity is imported.
    pub fn is_imported(&self) -> bool {
        matches!(self, Self::Imported(_))
    }

    /// Returns `true` if the entity is defined.
    pub fn is_defined(&self) -> bool {
        matches!(self, Self::Defined(_))
    }

    /// Returns `Some` entity if the entity is defined.
    ///
    /// Returns `None` in case the entity is imported.
    pub fn filter_map_defined(
        self,
    ) -> Option<DefinedEntityMut<'a, Id, Decl, Def>> {
        if let Self::Defined(defined_entity) = self {
            return Some(defined_entity)
        }
        None
    }
}

/// A mutable reference to an imported entity.
#[derive(Debug, PartialEq, Eq)]
pub struct ImportedEntityMut<'a, Id, Decl> {
    /// The unique ID of the imported entity.
    pub id: Id,
    /// The import name of the imported entity.
    pub name: &'a mut ImportName,
    /// The declaration of the imported entity.
    pub decl: &'a mut Decl,
}

/// A mutable reference to a defined entity.
#[derive(Debug, PartialEq, Eq)]
pub struct DefinedEntityMut<'a, Id, Decl, Def> {
    /// The unique ID of the defined entity.
    pub id: Id,
    /// The declaration of the defined entity.
    pub decl: &'a mut Decl,
    /// The definition of the defined entity.
    pub def: &'a mut Def,
}
