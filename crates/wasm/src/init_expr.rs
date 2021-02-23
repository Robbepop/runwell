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

use super::{Const, Error};
use core::convert::TryFrom;
use derive_more::{Display, Error};
use entity::RawIdx;
use ir::primitive::IntConst;
use module::primitive::Global;
use wasmparser::Operator;

/// An error that can occur upon parsing a global initializer expression.
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub enum InitExprError {
    /// Encountered a generic unsupported operator.
    #[display(fmt = "encountered an unsupported Wasm operator")]
    UnsupportedOperator,
    /// Encountered an unsupported `V128` type operator.
    #[display(fmt = "encountered an unsupported V128 type operator")]
    UnsupportedV128,
    /// Encountered an unsupported reference type operator.
    #[display(fmt = "encountered an unsupported reference type operator")]
    UnsupportedRefType,
    /// Encountered a malformed initializer expression.
    #[display(fmt = "encountered a malformatted initializer expression")]
    MalformedExpression,
}

/// A parsed and validated Wasm constant initializer expression.
#[derive(Debug)]
pub struct InitExpr {
    /// A Wasm translated Runwell initializer expression.
    inner: module::primitive::InitExpr,
}

impl InitExpr {
    /// Returns the inner Runwell initializer expression.
    pub fn into_inner(self) -> module::primitive::InitExpr {
        self.inner
    }
}

impl<'a> TryFrom<wasmparser::InitExpr<'a>> for InitExpr {
    type Error = Error;

    fn try_from(
        init_expr: wasmparser::InitExpr<'a>,
    ) -> Result<Self, Self::Error> {
        let mut init_expr_reader = init_expr.get_binary_reader();
        let init_expr = match init_expr_reader.read_operator()? {
            Operator::I32Const { value } => {
                module::primitive::InitExpr::Const(IntConst::I32(value).into())
            }
            Operator::I64Const { value } => {
                module::primitive::InitExpr::Const(IntConst::I64(value).into())
            }
            Operator::F32Const { value } => {
                module::primitive::InitExpr::Const(
                    Const::from(value).into_inner(),
                )
            }
            Operator::F64Const { value } => {
                module::primitive::InitExpr::Const(
                    Const::from(value).into_inner(),
                )
            }
            Operator::GlobalGet { global_index } => {
                module::primitive::InitExpr::GlobalGet(Global::from_raw(
                    RawIdx::from_u32(global_index),
                ))
            }
            Operator::V128Const { .. } => {
                return Err(InitExprError::UnsupportedV128).map_err(Into::into)
            }
            Operator::RefNull { .. } | Operator::RefFunc { .. } => {
                return Err(InitExprError::UnsupportedRefType)
                    .map_err(Into::into)
            }
            ref _unsupported => {
                return Err(InitExprError::UnsupportedOperator)
                    .map_err(Into::into)
            }
        };
        if !matches!(init_expr_reader.read_operator()?, Operator::End) {
            return Err(InitExprError::MalformedExpression).map_err(Into::into)
        }
        Ok(InitExpr { inner: init_expr })
    }
}
