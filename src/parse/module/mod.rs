// Copyright 2019 Robin Freyler
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
mod iter;

pub use self::{
    builder::ModuleBuilder,
    iter::{InternalFnIter, InternalGlobalIter},
};

use crate::parse::{
    utils::ImportedOrInternal,
    Function,
    FunctionBody,
    FunctionId,
    FunctionSig,
    FunctionSigId,
    GlobalVariable,
    GlobalVariableDecl,
    GlobalVariableId,
    Identifier,
    Initializer,
    LinearMemoryId,
    TableId,
};
use wasmparser::{Data, Export, MemoryType, TableType};

/// A parsed and validated WebAssembly (Wasm) module.
///
/// Use the [`parse`][`crate::parse::parse`] function in order to retrieve an instance of this type.
#[derive(Debug)]
pub struct Module<'a> {
    /// Function signature table.
    signatures: Vec<FunctionSig>,

    /// Imported and internal function signatures.
    fn_sigs: ImportedOrInternal<'a, FunctionSigId, FunctionId>,
    /// Imported and internal global variables.
    globals: ImportedOrInternal<'a, GlobalVariableDecl, GlobalVariableId>,
    /// Imported and internal linear memory sections.
    linear_memories: ImportedOrInternal<'a, MemoryType, LinearMemoryId>,
    /// Imported and internal tables.
    tables: ImportedOrInternal<'a, TableType, TableId>,

    /// Export definitions.
    exports: Vec<Export<'a>>,

    /// Optional start function.
    ///
    /// # Note
    ///
    /// If this is `Some` the Wasm module is an executable,
    /// otherwise it is a library.
    start_fn: Option<FunctionId>,

    // TODO: https://github.com/Robbepop/runwell/issues/1
    // /// Elements from the Wasm module.
    // elements: Vec<Element<'a>>,
    /// Internal function bodies.
    fn_bodies: Vec<FunctionBody<'a>>,
    /// Internal global definitions.
    globals_initializers: Vec<Initializer<'a>>,
    /// Internal table initializers.
    table_initializers: Vec<Initializer<'a>>,

    /// Generic data of the Wasm module.
    ///
    /// # Note
    ///
    /// Used to initialize the linear memory section.
    data: Vec<Data<'a>>,
}

impl<'a> Module<'a> {
    /// Returns the function signature identified by `id`.
    fn get_signature(&self, id: FunctionSigId) -> &FunctionSig {
        &self.signatures[id.get()]
    }

    /// Returns the function identified by `id`.
    pub fn get_fn(&self, id: FunctionId) -> Function {
        let fn_sig = self.get_signature(self.fn_sigs[id]);
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
    pub fn get_global(&self, id: GlobalVariableId) -> GlobalVariable {
        let decl = self.globals[id];
        GlobalVariable::new(id, decl)
    }

    /// Returns the global variable initializer expression identified by `id`.
    ///
    /// Returns `None` if the identified global variable is imported.
    pub fn get_global_initializer(
        &self,
        id: GlobalVariableId,
    ) -> Option<&Initializer<'a>> {
        id.get()
            .checked_sub(self.globals.len_imported())
            .map(|internal_id| &self.globals_initializers[internal_id])
    }

    /// Returns an iterator over all internal functions and their bodies.
    pub fn iter_internal_fns(&self) -> InternalFnIter {
        InternalFnIter::new(self)
    }

    /// Returns an iterator over all internal global variables and their
    /// initializer expressions.
    pub fn iter_internal_globals(&self) -> InternalGlobalIter {
        InternalGlobalIter::new(self)
    }

}

impl<'a> Module<'a> {
    /// Creates a new empty Wasm module.
    fn new() -> Self {
        Self {
            signatures: Vec::new(),
            fn_sigs: ImportedOrInternal::new(),
            globals: ImportedOrInternal::new(),
            linear_memories: ImportedOrInternal::new(),
            tables: ImportedOrInternal::new(),
            exports: Vec::new(),
            start_fn: None,
            fn_bodies: Vec::new(),
            globals_initializers: Vec::new(),
            table_initializers: Vec::new(),
            data: Vec::new(),
        }
    }

    /// Helps to build up a new Wasm module.
    pub(super) fn build() -> ModuleBuilder<'a> {
        ModuleBuilder::new(Self::new())
    }
}
