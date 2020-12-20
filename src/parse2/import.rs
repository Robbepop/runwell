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

use derive_more::{Display, Error};

/// An error upon parsing, validating or operating on Wasm imports.
#[derive(Debug, Error, Display, PartialEq, Eq, Hash)]
pub enum ImportError {
    #[display(fmt = "encountered unsupported Wasm module import")]
    UnsupportedModuleImport,
    #[display(fmt = "encountered unsupported Wasm event import")]
    UnsupportedEventImport,
}

/// The module and field name of an imported Wasm entity.
#[derive(Debug)]
pub struct ImportName<'a> {
    module_name: &'a str,
    field_name: &'a str,
}

impl<'a> ImportName<'a> {
    /// Creates a new import name from the given module and field names.
    pub fn new(module_name: &'a str, field_name: &'a str) -> Self {
        Self { module_name, field_name }
    }

    /// Returns the module name of the import.
    pub fn module_name(&self) -> &str {
        &self.module_name
    }

    /// Returns the field name of the import.
    pub fn field_name(&self) -> &str {
        &self.field_name
    }
}
