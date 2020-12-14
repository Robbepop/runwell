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

use crate::parse::{id::GlobalVariableId, CompilerError};
use core::convert::TryFrom;
use derive_more::Display;
use wasmparser::Operator;

/// An error that can occure upon parsing a global initializer expression.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum GlobalInitError {
    /// Encountered a generic unsupported operator.
    #[display(fmt = "encountered an unsupported Wasm operator")]
    UnsupportedOperator,
    /// Encountered an unsupported `f32` or `f64` type operator.
    #[display(fmt = "encountered an unsupported f32 or f64 type operator")]
    UnsupportedFloats,
    /// Encountered an unsupported `V128` type operator.
    #[display(fmt = "encountered an unsupported V128 type operator")]
    UnsupportedV128,
    /// Encountered an unsupported reference type operator.
    #[display(fmt = "encountered an unsupported reference type operator")]
    UnsupportedRefType,
    /// Encountered a malformatted initializer expression.
    #[display(fmt = "encountered a malformatted initializer expression")]
    InvalidExpression,
}

impl GlobalInitError {
    /// Returns `true` if the error states that some unsupported Wasm definition has been encountered.
    pub fn is_unsupported_error(&self) -> bool {
        match self {
            Self::UnsupportedOperator
            | Self::UnsupportedFloats
            | Self::UnsupportedV128
            | Self::UnsupportedRefType => true,
            _ => false,
        }
    }
}

#[derive(Debug, Display, Clone)]
pub enum GlobalInitExpr {
    #[display(fmt = "i32.const {}", _0)]
    I32Const(i32),
    #[display(fmt = "i64.const {}", _0)]
    I64Const(i64),
    #[display(fmt = "global.get {}", "_0.into_u32()")]
    GetGlobal(GlobalVariableId),
}

impl<'a> TryFrom<wasmparser::InitExpr<'a>> for GlobalInitExpr {
    type Error = CompilerError;

    fn try_from(
        init_expr: wasmparser::InitExpr<'a>,
    ) -> Result<Self, Self::Error> {
        let mut init_expr_reader = init_expr.get_binary_reader();
        let initializer = match init_expr_reader.read_operator()? {
            Operator::I32Const { value } => GlobalInitExpr::I32Const(value),
            Operator::I64Const { value } => GlobalInitExpr::I64Const(value),
            Operator::GlobalGet { global_index } => {
                GlobalInitExpr::GetGlobal(GlobalVariableId::from_u32(
                    global_index,
                ))
            }
            Operator::F32Const { .. } | Operator::F64Const { .. } => {
                return Err(GlobalInitError::UnsupportedFloats.into())
            }
            Operator::V128Const { .. } => {
                return Err(GlobalInitError::UnsupportedV128.into())
            }
            Operator::RefNull { .. } | Operator::RefFunc { .. } => {
                return Err(GlobalInitError::UnsupportedRefType.into())
            }
            ref _unsupported => {
                return Err(GlobalInitError::UnsupportedOperator.into())
            }
        };
        if !matches!(init_expr_reader.read_operator()?, Operator::End) {
            return Err(GlobalInitError::InvalidExpression.into())
        }
        Ok(initializer)
    }
}

#[test]
fn display_works() {
    assert_eq!(GlobalInitExpr::I32Const(1).to_string(), "i32.const 1");
    assert_eq!(GlobalInitExpr::I32Const(-1).to_string(), "i32.const -1");
    assert_eq!(GlobalInitExpr::I64Const(1).to_string(), "i64.const 1");
    assert_eq!(GlobalInitExpr::I64Const(-1).to_string(), "i64.const -1");
}
