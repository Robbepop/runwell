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

use crate::{global_var::Global, module::res::ModuleResources};
use ir::primitive::{Func, Mem, Table};

/// A slightly more efficient hash set using `ahash` random state.
type HashSet<T> = std::collections::HashSet<T, ahash::RandomState>;

/// Constructs module exports.
#[derive(Debug)]
pub struct ModuleExportsBuilder<'a> {
    res: &'a mut ModuleResources,
    /// Used to check for conflicting exported items.
    used_names: HashSet<ExportName>,
}

/// The name and kind of an exported item.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ExportName {
    name: String,
    kind: ExportKind,
}

/// The kind of an exported item.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ExportKind {
    Function,
    Table,
    Memory,
    Global,
}

impl<'a> ModuleExportsBuilder<'a> {
    /// Creates a new module exports builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self {
            res,
            used_names: Default::default(),
        }
    }

    /// Ensures that there are no conflicting export items.
    fn ensure_conflict_free(
        &mut self,
        kind: ExportKind,
        name: &str,
    ) -> Result<(), String> {
        if self.used_names.contains(&ExportName {
            kind,
            name: name.to_string(),
        }) {
            return Err(format!(
                "encountered conflicting export names: {} for kind {:?}",
                name, kind
            ))
        }
        Ok(())
    }

    /// Pushes a new function export.
    pub fn export_function(
        &mut self,
        idx: Func,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Function, name)?;
        self.res.function_export.insert(idx, name.to_string());
        Ok(())
    }

    /// Pushes a new table export.
    pub fn export_table(
        &mut self,
        idx: Table,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Table, name)?;
        self.res.table_export.insert(idx, name.to_string());
        Ok(())
    }

    /// Pushes a new linear memory export.
    pub fn export_memory(
        &mut self,
        idx: Mem,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Memory, name)?;
        self.res.memory_export.insert(idx, name.to_string());
        Ok(())
    }

    /// Pushes a new global variable export.
    pub fn export_global(
        &mut self,
        idx: Global,
        name: &str,
    ) -> Result<(), String> {
        self.ensure_conflict_free(ExportKind::Global, name)?;
        self.res.global_export.insert(idx, name.to_string());
        Ok(())
    }
}
