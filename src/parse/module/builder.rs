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
    FunctionBody,
    FunctionId,
    FunctionSig,
    FunctionSigId,
    GlobalVariableDecl,
    Initializer,
    Module,
    ParseError,
};
use wasmparser::{Data, Export, MemoryType, TableType};

/// A builder interface for a Wasm module.
///
/// Allows to mutate a module through some dedicated interfaces.
/// Used by the internal Wasm parser.
pub struct ModuleBuilder<'a> {
    /// The Wasm module that is being build.
    module: Module<'a>,
}

impl<'a> ModuleBuilder<'a> {
    /// Creates a new module builder for the given module.
    pub(super) fn new(module: Module<'a>) -> Self {
        Self { module }
    }

    /// Pushes the signature to the Wasm module.
    pub fn push_fn_signature(&mut self, sig: FunctionSig) {
        self.module.signatures.push(sig);
    }

    /// Pushes a new imported function to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported function is pushed after an internal
    /// function has already been pushed to the same Wasm module.
    pub fn push_imported_fn(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), ParseError> {
        self.module
            .fn_sigs
            .push_imported(module_name, field_name, fn_sig_id)
    }

    /// Pushes a new internal function to the Wasm module.
    pub fn push_internal_fn(&mut self, fn_sig_id: FunctionSigId) {
        self.module.fn_sigs.push_internal(fn_sig_id)
    }

    /// Pushes a new imported global variable to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported global variable is pushed after an internal
    /// global variable has already been pushed to the same Wasm module.
    pub fn push_imported_global(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        global: GlobalVariableDecl,
    ) -> Result<(), ParseError> {
        self.module
            .globals
            .push_imported(module_name, field_name, global)
    }

    /// Pushes a new internal global variable to the Wasm module.
    pub fn push_internal_global(&mut self, global: GlobalVariableDecl) {
        self.module.globals.push_internal(global)
    }

    /// Pushes a new imported linear memory to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported linear memory is pushed after an internal
    /// linear memory has already been pushed to the same Wasm module.
    pub fn push_imported_linear_memory(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        memory: MemoryType,
    ) -> Result<(), ParseError> {
        self.module.linear_memories.push_imported(
            module_name,
            field_name,
            memory,
        )
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn push_internal_linear_memory(&mut self, memory: MemoryType) {
        self.module.linear_memories.push_internal(memory)
    }

    /// Pushes a new imported table to the Wasm module.
    ///
    /// # Errors
    ///
    /// Errors if an imported table is pushed after an internal
    /// table has already been pushed to the same Wasm module.
    pub fn push_imported_table(
        &mut self,
        module_name: &'a str,
        field_name: &'a str,
        table: TableType,
    ) -> Result<(), ParseError> {
        self.module
            .tables
            .push_imported(module_name, field_name, table)
    }

    /// Pushes a new internal linear memory to the Wasm module.
    pub fn push_internal_table(&mut self, table: TableType) {
        self.module.tables.push_internal(table)
    }

    /// Pushes a new export to the Wasm module.
    pub fn push_export(&mut self, export: Export<'a>) {
        self.module.exports.push(export)
    }

    /// Sets the start function to the given function ID.
    pub fn set_start_fn(&mut self, id: FunctionId) {
        assert!(self.module.start_fn.is_none());
        self.module.start_fn = Some(id);
    }

    /// Pushes a new function body of an internal function to the Wasm module.
    pub fn push_fn_body(&mut self, fn_body: FunctionBody<'a>) {
        self.module.fn_bodies.push(fn_body)
    }

    /// Pushes a new internal global variable initializer expression
    /// to the Wasm module.
    pub fn push_global_initializer(&mut self, initializer: Initializer<'a>) {
        self.module.globals_initializers.push(initializer)
    }

    /// Pushes a new internal table initializer expression
    /// to the Wasm module.
    pub fn push_table_initializer(&mut self, initializer: Initializer<'a>) {
        self.module.table_initializers.push(initializer)
    }

    /// Pushes a new data definition to the Wasm module.
    pub fn push_data(&mut self, data: Data<'a>) {
        self.module.data.push(data)
    }

    /// Finalizes building of the Wasm module.
    pub fn finalize(self) -> Module<'a> {
        self.module
    }
}
