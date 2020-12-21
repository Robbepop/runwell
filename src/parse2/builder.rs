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
    GlobalVariableId,
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

/// Types implementing this trait can build up Wasm modules via the [`parse`][`crate::parse2::parse`] function.
///
/// This trait allows to decouple parsing from module building.
/// A module built this way can be used to instantiate concrete Wasm instances for execution.
pub trait ModuleBuilder {
    type Error: Into<ParseErrorKind>;
    type Module;

    fn reserve_types(&mut self, total_count: u32) -> Result<(), Self::Error>;

    fn define_type(&mut self, function_type: FunctionType) -> Result<(), Self::Error>;

    fn import_global(
        &mut self,
        import_name: ImportName,
        global: GlobalVariable,
    ) -> Result<(), Self::Error>;

    fn import_memory(
        &mut self,
        import_name: ImportName,
        memory: LinearMemory,
    ) -> Result<(), Self::Error>;

    fn import_table(
        &mut self,
        import_name: ImportName,
        table: Table,
    ) -> Result<(), Self::Error>;

    fn import_function(
        &mut self,
        import_name: ImportName,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), Self::Error>;

    fn reserve_functions(
        &mut self,
        total_count: u32,
    ) -> Result<(), Self::Error>;

    fn declare_function(
        &mut self,
        fn_sig_id: FunctionSigId,
    ) -> Result<(), Self::Error>;

    fn reserve_tables(&mut self, total_count: u32) -> Result<(), Self::Error>;

    fn declare_table(&mut self, table: Table) -> Result<(), Self::Error>;

    fn reserve_memories(&mut self, total_count: u32)
        -> Result<(), Self::Error>;

    fn declare_memory(
        &mut self,
        memory: LinearMemory,
    ) -> Result<(), Self::Error>;

    fn reserve_globals(&mut self, total_count: u32) -> Result<(), Self::Error>;

    fn define_global(
        &mut self,
        decl: GlobalVariable,
        init_value: InitializerExpr,
    ) -> Result<GlobalVariableId, Self::Error>;

    fn declare_export(&mut self, export: Export);

    fn set_start_fn(&mut self, id: FunctionId);

    fn reserve_elements(&mut self, total_count: u32)
        -> Result<(), Self::Error>;

    fn define_element(&mut self, element: Element) -> Result<(), Self::Error>;

    fn reserve_function_bodies(
        &mut self,
        total_count: u32,
    ) -> Result<(), Self::Error>;

    fn define_function_body(
        &mut self,
        fn_body: FunctionBody,
    ) -> Result<(), Self::Error>;

    fn reserve_datas(&mut self, total_count: u32) -> Result<(), Self::Error>;

    fn define_data(&mut self, data: Data) -> Result<(), Self::Error>;

    fn finalize(self) -> Result<Self::Module, Self::Error>;
}
