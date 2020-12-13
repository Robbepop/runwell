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

use super::definitions::ImportedOrDefined;
use crate::parse::{
    GlobalInitExpr,
    GlobalVariableDecl,
    GlobalVariableId,
    ComilerError,
};
use derive_more::Display;
use std::collections::BTreeSet;

/// An evaluation context for initializer expressions.
#[derive(Debug)]
pub struct EvaluationContext<'a> {
    globals: &'a ImportedOrDefined<
        GlobalVariableId,
        GlobalVariableDecl,
        GlobalInitExpr,
    >,
    resolving: BTreeSet<GlobalVariableId>,
}

pub type Globals =
    ImportedOrDefined<GlobalVariableId, GlobalVariableDecl, GlobalInitExpr>;

impl<'a> From<&'a Globals> for EvaluationContext<'a> {
    fn from(globals: &'a Globals) -> Self {
        Self {
            globals,
            resolving: Default::default(),
        }
    }
}

#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EvaluationError {
    InvalidConstInstruction,
    UnknownGlobalVariableId,
    ResolveCycle,
}

impl<'a> EvaluationContext<'a> {
    /// Internal implementation to resolve a global initializer expression using the context.
    fn eval_const_i32_impl(
        &mut self,
        expr: &GlobalInitExpr,
    ) -> Result<i32, ComilerError> {
        match expr {
            GlobalInitExpr::I32Const(value) => Ok(*value),
            GlobalInitExpr::I64Const(_value) => {
                Err(EvaluationError::InvalidConstInstruction)
                    .map_err(Into::into)
            }
            GlobalInitExpr::GetGlobal(id) => {
                if self.resolving.insert(*id) {
                    return Err(EvaluationError::ResolveCycle)
                        .map_err(Into::into)
                }
                let resolved_expr = self
                    .globals
                    .get_defined(*id)
                    .ok_or(ComilerError::Evaluation(
                        EvaluationError::UnknownGlobalVariableId,
                    ))?
                    .def;
                let result = self.eval_const_i32_impl(resolved_expr)?;
                self.resolving.remove(id);
                Ok(result)
            }
        }
    }

    /// Evaluates the given initializer expression as constant `i32`.
    pub fn eval_const_i32(
        &mut self,
        expr: &GlobalInitExpr,
    ) -> Result<i32, ComilerError> {
        self.resolving.clear();
        let result = self.eval_const_i32_impl(expr)?;
        Ok(result)
    }
}
