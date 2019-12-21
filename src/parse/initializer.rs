// Copyright 2019 Robin Freyler
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

use crate::parse::{Operator, ParseError};

/// A Wasm initializer expression.
#[derive(Debug)]
pub struct Initializer {
    /// The operators of the initializer expression.
    ops: Vec<Operator>,
}

impl Initializer {
    /// Returns the operations of the initializer routine.
    pub fn ops(&self) -> &[Operator] {
        &self.ops
    }
}

impl<'a> core::convert::TryFrom<wasmparser::InitExpr<'a>> for Initializer {
    type Error = ParseError;

    fn try_from(
        init_expr: wasmparser::InitExpr<'a>,
    ) -> Result<Self, Self::Error> {
        Ok(Self {
            ops: init_expr
                .get_operators_reader()
                .into_iter()
                .map(|op| Operator::try_from(op?))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}
