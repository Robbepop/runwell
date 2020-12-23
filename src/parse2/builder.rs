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

use super::{
    Data,
    Element,
    Export,
    FunctionBody,
    FunctionId,
    FunctionSigId,
    FunctionType,
    GlobalVariable,
    ImportName,
    InitializerExpr,
    LinearMemory,
    ParseErrorKind,
    Table,
};
use derive_more::{Display, Error};

/// An error that occured while building up the Wasm module.
#[derive(Debug, Display, Error)]
pub struct BuilderError {}

/// Defines the error that can occure upon building the Wasm module.
pub trait BuildError {
    type Error: Into<ParseErrorKind>;
}

/// Types implementing this trait can build up Wasm modules via the
/// [`parse`][`crate::parse2::parse`] function.
///
/// This trait allows to decouple parsing from module building.
/// A module built this way can be used to instantiate concrete
/// Wasm instances for execution.
pub trait ModuleBuilder: BuildError {
    /// The concrete type of the built Wasm module.
    type Module;

    /// The gate type to push new type definitions to the Wasm module.
    type TypeSection: DefineType<Error = Self::Error>;
    /// Returns a gate to push new type definitions to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::import_section`].
    fn type_section(
        &mut self,
        count_types: u32,
    ) -> Result<Self::TypeSection, Self::Error>;

    /// The gate type to push new imports to the Wasm module.
    type ImportSection: ImportEntity<Error = Self::Error>;
    /// Returns a gate to push new imports to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::function_section`].
    fn import_section(
        &mut self,
        count_imports: u32,
    ) -> Result<Self::ImportSection, Self::Error>;

    /// The gate type to push new function declarations to the Wasm module.
    type FunctionSection: DeclareFunction<Error = Self::Error>;
    /// Returns a gate to push new function declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::table_section`].
    fn function_section(
        &mut self,
        count_functions: u32,
    ) -> Result<Self::FunctionSection, Self::Error>;

    /// The gate type to push new table declarations to the Wasm module.
    type TableSection: DeclareTable<Error = Self::Error>;
    /// Returns a gate to push new table declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::memory_section`].
    fn table_section(
        &mut self,
        count_tables: u32,
    ) -> Result<Self::TableSection, Self::Error>;

    /// The gate type to push new linear memory declarations to the Wasm module.
    type MemorySection: DeclareMemory<Error = Self::Error>;
    /// Returns a gate to push new linear memory declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::global_section`].
    fn memory_section(
        &mut self,
        count_memories: u32,
    ) -> Result<Self::MemorySection, Self::Error>;

    /// The gate type to push new global variable definitions to the Wasm module.
    type GlobalSection: DefineGlobal<Error = Self::Error>;
    /// Returns a gate to push new global variable definition to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::export_section`].
    fn global_section(
        &mut self,
        count_globals: u32,
    ) -> Result<Self::GlobalSection, Self::Error>;

    /// The gate type to push new export declarations to the Wasm module.
    type ExportSection: DeclareExport<Error = Self::Error>;
    /// Returns a gate to push new export declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::start_function`].
    fn export_section(
        &mut self,
        count_exports: u32,
    ) -> Result<Self::ExportSection, Self::Error>;

    /// Sets the start function to be executed for module instantiation.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::element_section`].
    fn start_function(&mut self, id: FunctionId);

    /// The gate type to push new element items to the Wasm module.
    type ElementSection: PushElement<Error = Self::Error>;
    /// Returns a gate to push new element items to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::code_section`].
    fn element_section(
        &mut self,
        count_elements: u32,
    ) -> Result<Self::ElementSection, Self::Error>;

    /// The gate type to push new function bodies to the Wasm module.
    type CodeSection: DefineFunctionBody<Error = Self::Error>;
    /// Returns a gate to push new function bodies to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::data_section`].
    fn code_section(
        &mut self,
        count_function_bodies: u32,
    ) -> Result<Self::CodeSection, Self::Error>;

    /// The gate type to push new data items to the Wasm module.
    type DataSection: PushData<Error = Self::Error>;
    /// Returns a gate to push new data items to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder2::finish`].
    fn data_section(
        &mut self,
        count_datas: u32,
    ) -> Result<Self::DataSection, Self::Error>;

    /// Finishes building the module by returning the built Wasm module.
    fn finish(self) -> Result<Self::Module, Self::Error>;
}

pub trait DefineType: BuildError {
    /// Defines a new type definition.
    ///
    /// # Note
    ///
    /// This is called once for every unique function type in the Wasm module.
    fn define_type(
        &mut self,
        function_type: FunctionType,
    ) -> Result<(), Self::Error>;
}

pub trait ImportEntity: BuildError {
    /// Imports a new global variable with the given name.
    fn import_global(
        &mut self,
        import_name: ImportName,
        global: GlobalVariable,
    ) -> Result<(), Self::Error>;

    /// Imports a new linear memory with the given name.
    fn import_memory(
        &mut self,
        import_name: ImportName,
        memory: LinearMemory,
    ) -> Result<(), Self::Error>;

    /// Imports a new table with the given name.
    fn import_table(
        &mut self,
        import_name: ImportName,
        table: Table,
    ) -> Result<(), Self::Error>;

    /// Imports a new function with the given name.
    fn import_function(
        &mut self,
        import_name: ImportName,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), Self::Error>;
}

pub trait DeclareFunction: BuildError {
    /// Pushes another function declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per function in the built Wasm module.
    fn declare_function(
        &mut self,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), Self::Error>;
}

pub trait DeclareTable: BuildError {
    /// Pushes another table declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per table in the built Wasm module.
    fn declare_table(&mut self, table: Table) -> Result<(), Self::Error>;
}

pub trait DeclareMemory: BuildError {
    /// Pushes another linear memory declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per table in the built Wasm module.
    fn declare_memory(&mut self, table: LinearMemory) -> Result<(), Self::Error>;
}

pub trait DefineGlobal: BuildError {
    /// Pushes another global variable definition to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per global variable in the built Wasm module.
    fn define_global(&mut self, variable: GlobalVariable, init_value: InitializerExpr) -> Result<(), Self::Error>;
}

pub trait DeclareExport: BuildError {
    /// Pushes another export declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per export declaration in the built Wasm module.
    fn declare_export(&mut self, export: Export) -> Result<(), Self::Error>;
}

pub trait PushElement: BuildError {
    /// Pushes another element for initialization of a table of the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per element item in the built Wasm module.
    fn push_element(&mut self, element: Element) -> Result<(), Self::Error>;
}

pub trait PushData: BuildError {
    /// Pushes another element for initialization of a linear memory of the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per data item in the built Wasm module.
    fn push_data(&mut self, data: Data) -> Result<(), Self::Error>;
}

pub trait DefineFunctionBody: BuildError {
    /// Pushes another function body definition to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per function body in the built Wasm module.
    fn define_function_body(&mut self, function_body: FunctionBody) -> Result<(), Self::Error>;
}
