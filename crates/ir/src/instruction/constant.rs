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
    primitive::{Const, FloatConst, IntConst, Type, Value, F32, F64},
    VisitValues,
    VisitValuesMut,
};
use derive_more::Display;

/// An instruction representing a constant value.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "const<{}> {}", "self.const_value.ty()", const_value)]
pub struct ConstInstr {
    const_value: Const,
}

impl ConstInstr {
    /// Creates a new constant instruction.
    pub fn new(const_value: Const) -> Self {
        Self { const_value }
    }

    /// Creates a new `i32` constant instruction.
    pub fn i32(value: i32) -> Self {
        Self {
            const_value: Const::Int(IntConst::I32(value)),
        }
    }

    /// Creates a new `i64` constant instruction.
    pub fn i64(value: i64) -> Self {
        Self {
            const_value: Const::Int(IntConst::I64(value)),
        }
    }

    /// Creates a new `f32` constant instruction.
    pub fn f32(value: F32) -> Self {
        Self {
            const_value: Const::Float(FloatConst::F32(value)),
        }
    }

    /// Creates a new `f64` constant instruction.
    pub fn f64(value: F64) -> Self {
        Self {
            const_value: Const::Float(FloatConst::F64(value)),
        }
    }

    /// Returns the type of the constant value of the constant instruction.
    #[inline]
    pub fn ty(&self) -> Type {
        self.const_value.ty()
    }

    /// Returns the constant value of the constant instruction.
    #[inline]
    pub fn const_value(&self) -> Const {
        self.const_value
    }
}

impl VisitValues for ConstInstr {
    fn visit_values<V>(&self, _visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
    }
}

impl VisitValuesMut for ConstInstr {
    fn visit_values_mut<V>(&mut self, _visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
    }
}
