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

use super::{
    primitive::{F32, F64},
    Value,
};
use crate::parse::{id::GlobalVariableId, CompilerError};
use core::convert::TryFrom;
use derive_more::Display;
use wasmparser::Operator;

/// An error that can occure upon parsing a global initializer expression.
#[derive(Debug, Display, PartialEq, Eq)]
pub enum InitializerExprError {
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

impl InitializerExprError {
    /// Returns `true` if the error states that some unsupported Wasm definition has been encountered.
    pub fn is_unsupported_error(&self) -> bool {
        matches!(
            self,
            Self::UnsupportedOperator
                | Self::UnsupportedFloats
                | Self::UnsupportedV128
                | Self::UnsupportedRefType
        )
    }
}

#[derive(Debug, Display, Clone)]
pub enum InitializerExpr {
    Const(Value),
    #[display(fmt = "global.get {}", "_0.into_u32()")]
    GetGlobal(GlobalVariableId),
}

impl InitializerExpr {
    /// Returns an `i32` value if the initializer expression
    /// represents a constant `i32` value.
    ///
    /// Otherwise returns `None`.
    ///
    /// # Note
    ///
    /// This does not take into account any evaluation context or
    /// values of global variables.
    pub fn get_if_const_i32(&self) -> Option<i32> {
        match self {
            Self::Const(Value::I32(value)) => Some(*value),
            _ => None,
        }
    }
}

impl<'a> TryFrom<wasmparser::InitExpr<'a>> for InitializerExpr {
    type Error = CompilerError;

    fn try_from(
        init_expr: wasmparser::InitExpr<'a>,
    ) -> Result<Self, Self::Error> {
        let mut init_expr_reader = init_expr.get_binary_reader();
        let initializer = match init_expr_reader.read_operator()? {
            Operator::I32Const { value } => {
                InitializerExpr::Const(Value::I32(value))
            }
            Operator::I64Const { value } => {
                InitializerExpr::Const(Value::I64(value))
            }
            Operator::F32Const { value } => {
                InitializerExpr::Const(F32::from(value).into())
            }
            Operator::F64Const { value } => {
                InitializerExpr::Const(F64::from(value).into())
            }
            Operator::GlobalGet { global_index } => {
                InitializerExpr::GetGlobal(GlobalVariableId::from_u32(
                    global_index,
                ))
            }
            Operator::V128Const { .. } => {
                return Err(InitializerExprError::UnsupportedV128.into())
            }
            Operator::RefNull { .. } | Operator::RefFunc { .. } => {
                return Err(InitializerExprError::UnsupportedRefType.into())
            }
            ref _unsupported => {
                return Err(InitializerExprError::UnsupportedOperator.into())
            }
        };
        if !matches!(init_expr_reader.read_operator()?, Operator::End) {
            return Err(InitializerExprError::InvalidExpression.into())
        }
        Ok(initializer)
    }
}

#[test]
fn display_works() {
    assert_eq!(
        InitializerExpr::Const(Value::I32(1)).to_string(),
        "i32.const 1"
    );
    assert_eq!(
        InitializerExpr::Const(Value::I32(-1)).to_string(),
        "i32.const -1"
    );
    assert_eq!(
        InitializerExpr::Const(Value::I64(1)).to_string(),
        "i64.const 1"
    );
    assert_eq!(
        InitializerExpr::Const(Value::I64(-1)).to_string(),
        "i64.const -1"
    );
}
