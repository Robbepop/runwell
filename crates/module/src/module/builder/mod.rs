// Copyright 2021 Robin Freyler
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

mod export;
mod function;
mod global;
mod import;
mod memory;
mod table;
mod types;

pub use self::{
    export::{ExportKind, ExportName, ModuleExportsBuilder},
    function::{ModuleFunctionBodiesBuilder, ModuleFunctionsBuilder},
    global::{GlobalInit, ModuleGlobalsBuilder},
    import::ModuleImportsBuilder,
    memory::{ModuleMemoriesBuilder, ModuleMemoryDataBuilder},
    table::{ModuleTableElementsBuilder, ModuleTablesBuilder},
    types::ModuleTypesBuilder,
};
use super::Module;

use super::res::ModuleResources;
use crate::FunctionBody;
use entity::ComponentVec;
use ir::primitive::Func;

/// A module builder to incrementally build up a Runwell module.
#[derive(Debug)]
pub struct ModuleBuilder {
    /// The last section that has been processed.
    section: Option<ModuleSection>,
    /// The internal resources of the constructed module.
    res: ModuleResources,
    /// The bodies (implementations) of the internal functions.
    bodies: ComponentVec<Func, FunctionBody>,
}

/// The Runwell module sections.
///
/// A Runwell module has to be constructed in the order of the
/// module sections listed with their discriminants below.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModuleSection {
    Types = 1,
    Imports = 2,
    Functions = 3,
    Tables = 4,
    Memories = 5,
    Globals = 6,
    Exports = 7,
    TableElements = 8,
    FunctionBodies = 9,
    MemoryData = 10,
}

impl ModuleBuilder {
    /// Creates a new module builder.
    pub(crate) fn new() -> Self {
        Self {
            section: None,
            res: Default::default(),
            bodies: Default::default(),
        }
    }

    /// Ensures that the module sections are constructed in the correct order.
    ///
    /// Updates the current module section if in order.
    fn ensure_section_in_order(
        &mut self,
        next: ModuleSection,
    ) -> Result<(), String> {
        let current = self.section.unwrap_or(ModuleSection::Types);
        if current > next {
            return Err(format!(
                "tried to construct module in incorrect order: {:?} followed after {:?}",
                next, current,
            ))
        }
        self.section = Some(next);
        Ok(())
    }

    /// Returns a module types builder.
    pub fn type_section(&mut self) -> Result<ModuleTypesBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Types)?;
        Ok(ModuleTypesBuilder::new(&mut self.res))
    }

    /// Returns a module imports builder.
    pub fn import_section(&mut self) -> Result<ModuleImportsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Imports)?;
        Ok(ModuleImportsBuilder::new(&mut self.res))
    }

    /// Returns a module function declaration builder.
    pub fn function_section(
        &mut self,
    ) -> Result<ModuleFunctionsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Functions)?;
        Ok(ModuleFunctionsBuilder::new(&mut self.res))
    }

    /// Returns a module table declaration builder.
    pub fn table_section(&mut self) -> Result<ModuleTablesBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Tables)?;
        Ok(ModuleTablesBuilder::new(&mut self.res))
    }

    /// Returns a module linear memory declaration builder.
    pub fn memory_section(&mut self) -> Result<ModuleMemoriesBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Memories)?;
        Ok(ModuleMemoriesBuilder::new(&mut self.res))
    }

    /// Returns a module global variable builder.
    pub fn global_section(&mut self) -> Result<ModuleGlobalsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Globals)?;
        Ok(ModuleGlobalsBuilder::new(&mut self.res))
    }

    /// Returns a module export builder.
    pub fn export_section(&mut self) -> Result<ModuleExportsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::Exports)?;
        Ok(ModuleExportsBuilder::new(&mut self.res))
    }

    /// Sets the start function of the module.
    ///
    /// The start function is executed before actual execution of the module.
    /// It is used to initialize certain structures before actual execution
    /// takes place.
    pub fn set_start_func(&mut self, start_func: Func) -> Result<(), String> {
        if let Some(old_start_func) = self.res.start_func {
            return Err(
                format!(
                    "tried to set start function to {:?} while the module already has a start function {:?}",
                    start_func,
                    old_start_func,
                )
            )
        }
        self.res.start_func = Some(start_func);
        Ok(())
    }

    /// Returns a module table elements builder.
    pub fn table_element_section(
        &mut self,
    ) -> Result<ModuleTableElementsBuilder, String> {
        self.ensure_section_in_order(ModuleSection::TableElements)?;
        Ok(ModuleTableElementsBuilder::new(&mut self.res))
    }

    /// Returns a module memory data builder.
    pub fn memory_data_section(
        &mut self,
    ) -> Result<ModuleMemoryDataBuilder, String> {
        self.ensure_section_in_order(ModuleSection::MemoryData)?;
        Ok(ModuleMemoryDataBuilder::new(&mut self.res))
    }

    /// Returns a module function bodies builder.
    pub fn code_section(
        &mut self,
    ) -> Result<(&ModuleResources, ModuleFunctionBodiesBuilder), String> {
        self.ensure_section_in_order(ModuleSection::FunctionBodies)?;
        let Self { res, bodies, .. } = self;
        let res = &*res;
        let builder = ModuleFunctionBodiesBuilder::new(res, bodies);
        Ok((res, builder))
    }

    /// Finalizes the construction of the module.
    ///
    /// # Errors
    ///
    /// If there are missing function bodies for declared internal functions.
    pub fn finalize(mut self) -> Result<Module, String> {
        let len_func_decls = self.res.function_decls.len();
        let len_func_imports = self.res.function_import.len();
        let len_func_bodies = self.bodies.len();
        if len_func_decls != len_func_bodies + len_func_imports {
            return Err(format!(
                "encountered mismatch with {} function bodies for {} function declarations",
                len_func_decls,
                len_func_bodies,
            ))
        }
        self.res.shrink_to_fit();
        self.bodies.shrink_to_fit();
        Ok(Module {
            res: self.res,
            bodies: self.bodies,
        })
    }
}
