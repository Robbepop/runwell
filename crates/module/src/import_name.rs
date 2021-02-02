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

/// A module and field name for an imported entity.
#[derive(Debug)]
pub struct ImportName {
    module_name: String,
    field_name: String,
}

impl ImportName {
    /// Creates a new import name.
    pub fn new(module_name: &str, field_name: &str) -> Self {
        Self {
            module_name: module_name.to_string(),
            field_name: field_name.to_string(),
        }
    }

    /// Returns the module name.
    pub fn module_name(&self) -> &str {
        &self.module_name
    }

    /// Returns the field name.
    pub fn field_name(&self) -> &str {
        &self.field_name
    }
}
