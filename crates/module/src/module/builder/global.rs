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

use crate::{
    global_var::{Global, GlobalVariable},
    module::res::ModuleResources,
    primitive::{ImportName, InitExpr},
};

/// A global variable initialization.
///
/// This either represents an imported global variable with its value
/// or an internal global variable with its definition.
#[derive(Debug)]
pub enum GlobalInit {
    Import(ImportName),
    Define(InitExpr),
}

/// Constructs internal module global variables.
#[derive(Debug)]
pub struct ModuleGlobalsBuilder<'a> {
    res: &'a mut ModuleResources,
}

impl<'a> ModuleGlobalsBuilder<'a> {
    /// Creates a new module globals builder.
    pub(super) fn new(res: &'a mut ModuleResources) -> Self {
        Self { res }
    }

    /// Reserves space for `additional` global variable.
    pub fn reserve(&mut self, additional: u32) {
        self.res.global_decls.reserve_exact(additional);
    }

    /// Pushes a new global variable to the module and returns an index to it.
    pub fn push_global(
        &mut self,
        decl: GlobalVariable,
        init: InitExpr,
    ) -> Result<Global, String> {
        let idx = self.res.global_entities.alloc(Default::default());
        self.res.global_decls.insert(idx, decl);
        self.res.global_inits.insert(idx, GlobalInit::Define(init));
        Ok(idx)
    }
}
