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

use crate::parse::{
    utils::MergedEntities,
    FunctionBody,
    FunctionId,
    FunctionSig,
    FunctionSigId,
    GlobalVariableDecl,
    GlobalVariableId,
    GlobalVariableInitializer,
    LinearMemoryId,
    ParseError,
    TableId,
};
use wasmparser::{Data, Element, Export, MemoryType, TableType};

pub type Initializer<'a> = GlobalVariableInitializer<'a>;

/// A parsed and validated WebAssembly (Wasm) module.
#[derive(Debug)]
pub struct Module<'a> {
    /// Function signature table.
    pub(super) signatures: Vec<FunctionSig>,

    /// Imported and internal function signatures.
    pub(super) fn_sigs: MergedEntities<'a, FunctionSigId, FunctionId>,
    /// Imported and internal global variables.
    pub(super) globals:
        MergedEntities<'a, GlobalVariableDecl, GlobalVariableId>,
    /// Imported and internal linear memory sections.
    pub(super) linear_memories: MergedEntities<'a, MemoryType, LinearMemoryId>,
    /// Imported and internal tables.
    pub(super) tables: MergedEntities<'a, TableType, TableId>,

    /// Export definitions.
    pub(super) exports: Vec<Export<'a>>,

    /// Optional start function.
    ///
    /// # Note
    ///
    /// If this is `Some` the Wasm module is an executable,
    /// otherwise it is a library.
    pub(super) start_fn: Option<FunctionId>,

    // TODO: We don't implement this because `wasmparser::Element`
    //       does not implement `core::fmt::Debug`.
    // /// Elements from the Wasm module.
    // pub(super) elements: Vec<Element<'a>>,

    /// Internal function bodies.
    pub(super) fn_bodies: Vec<FunctionBody<'a>>,
    /// Internal global definitions.
    pub(super) globals_initializers: Vec<Initializer<'a>>,
    /// Internal table initializers.
    pub(super) table_initializers: Vec<Initializer<'a>>,

    /// Generic data of the Wasm module.
    pub(super) data: Vec<Data<'a>>,
}

impl Default for Module<'_> {
    fn default() -> Self {
        Module::new()
    }
}

impl<'a> Module<'a> {
    /// Creates a new empty Wasm module.
    pub fn new() -> Self {
        Self {
            signatures: Vec::new(),
            fn_sigs: MergedEntities::new(),
            globals: MergedEntities::new(),
            linear_memories: MergedEntities::new(),
            tables: MergedEntities::new(),
            exports: Vec::new(),
            start_fn: None,
            fn_bodies: Vec::new(),
            globals_initializers: Vec::new(),
            table_initializers: Vec::new(),
            data: Vec::new(),
        }
    }
}
