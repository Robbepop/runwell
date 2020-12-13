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

mod builder;
mod definitions;
mod eval_context;
mod export;
mod iter;
mod linear_memory;
mod table;
mod types;

pub use self::{
    builder::{BuildError, ModuleBuilder},
    definitions::{
        DefinedEntity,
        DefinedEntityIter,
        DefinedEntityMut,
        Entity,
        EntityIter,
        EntityMut,
        ImportName,
        ImportedEntity,
        ImportedEntityIter,
        ImportedEntityMut,
        ImportedOrDefined,
        ModuleError,
    },
    eval_context::{EvaluationContext, EvaluationError},
    export::{Export, ExportError, ExportItem, ExportKind, Exports},
    iter::InternalFnIter,
    linear_memory::{
        Data,
        LinearMemoryContents,
        LinearMemoryDecl,
        MemoryError,
    },
    table::{Element, ElementItemsIter, TableDecl, TableItems},
    types::{FunctionSig, Types, TypesError, UnsupportedTypeDef},
};
use crate::parse::{
    Function,
    FunctionBody,
    FunctionId,
    FunctionSigId,
    GlobalInitExpr,
    GlobalVariableDecl,
    GlobalVariableId,
    Identifier,
    LinearMemoryId,
    TableId,
};

/// An iterator yielding global variables.
pub type GlobalVariableIter<'a> =
    EntityIter<'a, GlobalVariableId, GlobalVariableDecl, GlobalInitExpr>;

/// A parsed and validated WebAssembly (Wasm) module.
///
/// Use the [`parse`][`crate::parse::parse`] function in order to retrieve an instance of this type.
///
/// # Note
///
/// This virtual Wasm module representation supports only the subset of WebAssembly that is important
/// for the Runwell JIT compiler. It organizes its definitions in arrays and allows to translate
/// Wasm function bodies concurrently.
#[derive(Debug)]
pub struct Module {
    /// Function signature table.
    ///
    /// # Note
    ///
    /// Represents the Wasm `type` section.
    types: Types,
    /// Imported and internal function signatures.
    ///
    /// # Note
    ///
    /// Represents both the Wasm `function` and `code` sections.
    /// Also holds information about imported function declarations.
    fn_sigs: ImportedOrDefined<FunctionId, FunctionSigId, ()>,
    /// Imported and internal global variables.
    ///
    /// # Note
    ///
    /// Represents the Wasm `global` section.
    /// Also holds information about imported global variables.
    globals:
        ImportedOrDefined<GlobalVariableId, GlobalVariableDecl, GlobalInitExpr>,
    /// Imported and internal linear memory sections.
    ///
    /// # Note
    ///
    /// Represents both the Wasm `memory` and `data` sections.
    /// Also holds information about imported linear memories.
    linear_memories: ImportedOrDefined<LinearMemoryId, LinearMemoryDecl, ()>,
    /// Imported and internal tables.
    ///
    /// # Note
    ///
    /// Represents both the Wasm `table` and `data` element.
    /// Also holds information about imported tables.
    tables: ImportedOrDefined<TableId, TableDecl, ()>,
    /// Export definitions.
    ///
    /// # Note
    ///
    /// Represents the Wasm `export` section.
    exports: Exports,
    /// Optional start function.
    ///
    /// # Note
    ///
    /// If this is `Some` the Wasm module is an executable,
    /// otherwise it is a library.
    start_fn: Option<FunctionId>,
    /// Internal function bodies.
    ///
    /// # Dev. Note
    ///
    /// Old and to-be-phased-out function bodies storage.
    /// We are going to move this into `fn_sigs` and obviously therefore rename `fn_sigs`.
    fn_bodies: Vec<FunctionBody>,
}

impl<'a> Module {
    /// Returns the function identified by `id`.
    pub fn get_fn(&self, id: FunctionId) -> Function {
        let fn_sig_id = self
            .fn_sigs
            .get(id)
            .expect("encountered unexpected invalid function ID")
            .decl()
            .clone();
        let fn_sig = self.types.get(fn_sig_id);
        Function::new(id, fn_sig)
    }

    /// Returns the function body identified by `id`.
    ///
    /// Returns `None` if the identified function is imported.
    ///
    /// # Note
    ///
    /// Required for utilities such as `start_fn`.
    pub fn get_fn_body(&self, id: FunctionId) -> Option<&FunctionBody> {
        id.get()
            // Convert the identified into an internal one.
            .checked_sub(self.fn_sigs.len_imported())
            .map(|internal_id| &self.fn_bodies[internal_id])
    }

    /// Returns the global variable identified by `id`.
    pub fn get_global(
        &self,
        id: GlobalVariableId,
    ) -> Entity<GlobalVariableId, GlobalVariableDecl, GlobalInitExpr> {
        self.globals
            .get(id)
            .expect("encountered unexpected invalid global variable ID")
    }

    /// Returns the linear memory identified by `id`.
    ///
    /// # Note
    ///
    /// Operations in Wasm that do not specify a linear memory ID explicitely
    /// are implicitely refering to the linear memory that is identified by
    /// the `0` ID. Use the
    /// [`Default`](https://doc.rust-lang.org/core/default/trait.Default.html)
    /// implementation of
    /// [`LinearMemoryId`][`crate::parse::LinearMemoryId`] in order to receive
    /// the implicit linear memory.
    ///
    /// ```no_run
    /// # let module: runwell::parse::Module = unimplemented!();
    /// let mem = module.get_linear_memory(Default::default());
    /// ```
    pub fn get_linear_memory(&self, id: LinearMemoryId) -> &LinearMemoryDecl {
        self.linear_memories
            .get(id)
            .expect("encountered unexpected invalid linear memory ID")
            .decl()
    }

    /// Returns the table identified by `id`.
    ///
    /// # Note
    ///
    /// Operations in Wasm that do not specify a table ID explicitely
    /// are implicitely refering to the table that is identified by
    /// the `0` ID. Use the
    /// [`Default`](https://doc.rust-lang.org/core/default/trait.Default.html)
    /// implementation of
    /// [`TableId`][`crate::parse::TableId`] in order to receive
    /// the implicit table.
    ///
    /// ```no_run
    /// # let module: runwell::parse::Module = unimplemented!();
    /// let table = module.get_table(Default::default());
    /// ```
    pub fn get_table(&self, id: TableId) -> Entity<TableId, TableDecl, ()> {
        self.tables
            .get(id)
            .expect("encountered unexpected invalid table ID")
    }

    /// Returns an iterator over all internal functions and their bodies.
    pub fn iter_internal_fns(&self) -> InternalFnIter {
        InternalFnIter::new(self)
    }

    /// Returns an iterator over all imported or defined global variables.
    pub fn iter_globals(&self) -> GlobalVariableIter {
        self.globals.iter().expect(
            "encountered unexpected error upon iterating global variables",
        )
    }

    /// Returns the start function of the Wasm module if any.
    pub fn start_fn(&self) -> Option<Function> {
        self.start_fn.map(|fn_id| self.get_fn(fn_id))
    }
}

impl<'a> Module {
    /// Creates a new empty Wasm module.
    fn new() -> Self {
        Self {
            types: Types::default(),
            fn_sigs: ImportedOrDefined::default(),
            globals: ImportedOrDefined::default(),
            linear_memories: ImportedOrDefined::default(),
            tables: ImportedOrDefined::default(),
            exports: Exports::default(),
            start_fn: None,
            fn_bodies: Vec::new(),
        }
    }

    /// Helps to build up a new Wasm module.
    pub(super) fn build() -> ModuleBuilder {
        ModuleBuilder::new(Self::new())
    }
}
