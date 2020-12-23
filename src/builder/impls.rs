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
    pub fn type_section(
        &mut self,
        count_types: u32,
    ) -> Result<DefineType, BuilderError> {
        Ok(self.into())
    }

    pub fn import_section(
        &mut self,
        count_imports: u32,
    ) -> Result<ImportEntity, BuilderError> {
        Ok(self.into())
    }

    pub fn function_section(
        &mut self,
        count_functions: u32,
    ) -> Result<DeclareFunction, BuilderError> {
        Ok(self.into())
    }

    pub fn table_section(
        &mut self,
        count_tables: u32,
    ) -> Result<DeclareTable, BuilderError> {
        Ok(self.into())
    }

    pub fn memory_section(
        &mut self,
        count_memories: u32,
    ) -> Result<DeclareMemory, BuilderError> {
        Ok(self.into())
    }

    pub fn global_section(
        &mut self,
        count_globals: u32,
    ) -> Result<DefineGlobal, BuilderError> {
        Ok(self.into())
    }

    pub fn export_section(
        &mut self,
        count_exports: u32,
    ) -> Result<DeclareExport, BuilderError> {
        Ok(self.into())
    }

    pub fn start_function(&mut self, _id: crate::parse2::FunctionId) {}

    pub fn element_section(
        &mut self,
        count_elements: u32,
    ) -> Result<PushElement, BuilderError> {
        Ok(self.into())
    }

    pub fn code_section_start(
        &mut self,
        count_function_bodies: u32,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    pub fn code_section_entry(
        &mut self,
        function_body: crate::parse2::FunctionBody,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    pub fn data_section(
        &mut self,
        count_datas: u32,
    ) -> Result<PushData, BuilderError> {
        Ok(self.into())
    }

    pub fn finish(self) -> Result<Module, BuilderError> {
        Ok(Module {})
    }
}

#[derive(Debug, From)]
pub struct DefineType<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DefineType<'a> {
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
    pub fn import_global(
        &mut self,
        import_name: crate::parse2::ImportName,
        global: crate::parse2::GlobalVariable,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    pub fn import_memory(
        &mut self,
        import_name: crate::parse2::ImportName,
        memory: crate::parse2::LinearMemory,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    pub fn import_table(
        &mut self,
        import_name: crate::parse2::ImportName,
        table: crate::parse2::Table,
    ) -> Result<(), BuilderError> {
        Ok(())
    }

    pub fn import_function(
        &mut self,
        import_name: crate::parse2::ImportName,
        fn_sig_id: crate::parse2::FunctionSigId,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}

#[derive(Debug, From)]
pub struct DeclareFunction<'a> {
    builder: &'a mut ModuleBuilder,
}

impl<'a> DeclareFunction<'a> {
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
    pub fn push_data(
        &mut self,
        data: crate::parse2::Data,
    ) -> Result<(), BuilderError> {
        Ok(())
    }
}
