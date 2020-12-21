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

#![allow(unused_variables)]

use crate::parse2::{ModuleBuilder, ParseErrorKind};
use super::BuildError;

/// Builds Wasm modules from binary Wasm inputs.
///
/// Implements the [`ModuleBuilder`] trait.
#[derive(Debug)]
pub struct Builder {

}

impl From<BuildError> for ParseErrorKind {
    fn from(_error: BuildError) -> Self {
        ParseErrorKind::Builder(crate::parse2::BuilderError {})
    }
}

impl ModuleBuilder for Builder {
    type Module = ();
    type Error = BuildError;

    fn reserve_types(&mut self, total_count: u32) -> Result<(), Self::Error> {
        todo!()
    }

    fn define_type(&mut self, function_type: crate::parse2::FunctionType) -> Result<(), Self::Error> {
        todo!()
    }

    fn import_global(
        &mut self,
        import_name: crate::parse2::ImportName,
        global: crate::parse2::GlobalVariable,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn import_memory(
        &mut self,
        import_name: crate::parse2::ImportName,
        memory: crate::parse2::LinearMemory,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn import_table(
        &mut self,
        import_name: crate::parse2::ImportName,
        table: crate::parse2::Table,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn import_function(
        &mut self,
        import_name: crate::parse2::ImportName,
        fn_sig_id: crate::parse2::FunctionSigId,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn reserve_functions(
        &mut self,
        total_count: u32,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn declare_function(
        &mut self,
        fn_sig_id: crate::parse2::FunctionSigId,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn reserve_tables(&mut self, total_count: u32) -> Result<(), Self::Error> {
        todo!()
    }

    fn declare_table(&mut self, table: crate::parse2::Table) -> Result<(), Self::Error> {
        todo!()
    }

    fn reserve_memories(&mut self, total_count: u32)
        -> Result<(), Self::Error> {
        todo!()
    }

    fn declare_memory(
        &mut self,
        memory: crate::parse2::LinearMemory,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn reserve_globals(&mut self, total_count: u32) -> Result<(), Self::Error> {
        todo!()
    }

    fn define_global(
        &mut self,
        decl: crate::parse2::GlobalVariable,
        init_value: crate::parse2::InitializerExpr,
    ) -> Result<crate::parse2::GlobalVariableId, Self::Error> {
        todo!()
    }

    fn declare_export(&mut self, export: crate::parse2::Export) {
        todo!()
    }

    fn set_start_fn(&mut self, id: crate::parse2::FunctionId) {
        todo!()
    }

    fn reserve_elements(&mut self, total_count: u32)
        -> Result<(), Self::Error> {
        todo!()
    }

    fn define_element(&mut self, element: crate::parse2::Element) -> Result<(), Self::Error> {
        todo!()
    }

    fn reserve_function_bodies(
        &mut self,
        total_count: u32,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn define_function_body(
        &mut self,
        fn_body: crate::parse2::FunctionBody,
    ) -> Result<(), Self::Error> {
        todo!()
    }

    fn reserve_datas(&mut self, total_count: u32) -> Result<(), Self::Error> {
        todo!()
    }

    fn define_data(&mut self, data: crate::parse2::Data) -> Result<(), Self::Error> {
        todo!()
    }

    fn finalize(self) -> Result<Self::Module, Self::Error> {
        todo!()
    }
}
