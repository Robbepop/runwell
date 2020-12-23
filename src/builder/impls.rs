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

use crate::parse2::FunctionBody;
use derive_more::From;

use super::BuilderError;

/// A parsed and validated Wasm module.
///
/// Used to create Wasm module instances for code execution.
#[derive(Debug)]
pub struct Module {}

/// Builds Wasm modules from binary Wasm inputs.
///
/// Implements the [`ModuleBuilder`] trait.
#[derive(Debug, Default)]
pub struct ModuleBuilder {}

impl ModuleBuilder {
    /// Returns a gate to push new type definitions to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::import_section`].
    pub fn type_section(
        &mut self,
        count_types: u32,
    ) -> Result<DefineType, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new imports to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::function_section`].
    pub fn import_section(
        &mut self,
        count_imports: u32,
    ) -> Result<ImportEntity, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new function declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::table_section`].
    pub fn function_section(
        &mut self,
        count_functions: u32,
    ) -> Result<DeclareFunction, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new table declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::memory_section`].
    pub fn table_section(
        &mut self,
        count_tables: u32,
    ) -> Result<DeclareTable, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new linear memory declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::global_section`].
    pub fn memory_section(
        &mut self,
        count_memories: u32,
    ) -> Result<DeclareMemory, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new global variable definition to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::export_section`].
    pub fn global_section(
        &mut self,
        count_globals: u32,
    ) -> Result<DefineGlobal, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new export declarations to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::start_function`].
    pub fn export_section(
        &mut self,
        count_exports: u32,
    ) -> Result<DeclareExport, BuilderError> {
        Ok(self.into())
    }

    /// Sets the start function to be executed for module instantiation.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::element_section`].
    pub fn start_function(&mut self, _id: crate::parse2::FunctionId) {}

    /// Returns a gate to push new element items to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::code_section`].
    pub fn element_section(
        &mut self,
        count_elements: u32,
    ) -> Result<PushElement, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new function bodies to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::data_section`].
    pub fn code_section(
        &mut self,
        count_function_bodies: u32,
    ) -> Result<DefineFunctionBody, BuilderError> {
        Ok(self.into())
    }

    /// Returns a gate to push new data items to the build module upon success.
    ///
    /// # Note
    ///
    /// Guaranteed to be called at most once and before any call to [`ModuleBuilder::finish`].
    pub fn data_section(
        &mut self,
        count_datas: u32,
    ) -> Result<PushData, BuilderError> {
        Ok(self.into())
    }

    /// Finishes building the module by returning the built Wasm module.
    pub fn finish(self) -> Result<Module, BuilderError> {
        Ok(Module {})
    }
}

#[derive(Debug, From)]
pub struct DefineType<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineType<'a> {
    /// Defines a new type definition.
    ///
    /// # Note
    ///
    /// This is called once for every unique function type in the Wasm module.
    pub fn define_type(
        &mut self,
        function_type: crate::parse2::FunctionType,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct ImportEntity<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> ImportEntity<'a> {
    /// Imports a new function with the given name.
    pub fn import_function(
        &mut self,
        import_name: crate::parse2::ImportName,
        fn_sig_id: crate::parse2::FunctionSigId,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    /// Imports a new global variable with the given name.
    pub fn import_global(
        &mut self,
        import_name: crate::parse2::ImportName,
        global: crate::parse2::GlobalVariable,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    /// Imports a new linear memory with the given name.
    pub fn import_memory(
        &mut self,
        import_name: crate::parse2::ImportName,
        memory: crate::parse2::LinearMemory,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    /// Imports a new table with the given name.
    pub fn import_table(
        &mut self,
        import_name: crate::parse2::ImportName,
        table: crate::parse2::Table,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareFunction<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareFunction<'a> {
    /// Pushes another function declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal function in the built Wasm module.
    pub fn declare_function(
        &mut self,
        fn_sig_id: crate::parse2::FunctionSigId,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareTable<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareTable<'a> {
    /// Pushes another table declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal table in the built Wasm module.
    pub fn declare_table(
        &mut self,
        table: crate::parse2::Table,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareMemory<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareMemory<'a> {
    /// Pushes another linear memory declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal linear memory in the built Wasm module.
    pub fn declare_memory(
        &mut self,
        table: crate::parse2::LinearMemory,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DefineGlobal<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineGlobal<'a> {
    /// Pushes another global variable definition to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per internal global variable in the built Wasm module.
    pub fn define_global(
        &mut self,
        variable: crate::parse2::GlobalVariable,
        init_value: crate::parse2::InitializerExpr,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareExport<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareExport<'a> {
    /// Pushes another export declaration to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per export declaration in the built Wasm module.
    pub fn declare_export(
        &mut self,
        export: crate::parse2::Export,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct PushElement<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> PushElement<'a> {
    /// Pushes another element for initialization of a table of the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per element item in the built Wasm module.
    pub fn push_element(
        &mut self,
        element: crate::parse2::Element,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct PushData<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> PushData<'a> {
    /// Pushes another element for initialization of a linear memory of the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per data item in the built Wasm module.
    pub fn push_data(
        &mut self,
        data: crate::parse2::Data,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DefineFunctionBody<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineFunctionBody<'a> {
    /// Pushes another function body definition to the Wasm module.
    ///
    /// # Note
    ///
    /// Guaranteed to be called once per function body in the built Wasm module.
    pub fn define_function_body(
        &mut self,
        function_body: FunctionBody,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}
