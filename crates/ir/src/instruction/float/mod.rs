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

mod binary;
mod fcmp;
mod fconv;
mod unary;

use crate::{primitive::Value, VisitValues, VisitValuesMut};

pub use self::{
    binary::{BinaryFloatInstr, BinaryFloatOp},
    fcmp::{CompareFloatInstr, CompareFloatOp},
    fconv::{DemoteFloatInstr, FloatToIntInstr, PromoteFloatInstr},
    unary::{UnaryFloatInstr, UnaryFloatOp},
};
use derive_more::{Display, From};

/// An SSA floating point number instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum FloatInstr {
    Unary(UnaryFloatInstr),
    Binary(BinaryFloatInstr),
    Compare(CompareFloatInstr),
    Demote(DemoteFloatInstr),
    Promote(PromoteFloatInstr),
    FloatToInt(FloatToIntInstr),
}

impl VisitValues for FloatInstr {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        match self {
            Self::Unary(instr) => instr.visit_values(visitor),
            Self::Binary(instr) => instr.visit_values(visitor),
            Self::Compare(instr) => instr.visit_values(visitor),
            Self::Demote(instr) => instr.visit_values(visitor),
            Self::Promote(instr) => instr.visit_values(visitor),
            Self::FloatToInt(instr) => instr.visit_values(visitor),
        }
    }
}

impl VisitValuesMut for FloatInstr {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        match self {
            Self::Unary(instr) => instr.visit_values_mut(visitor),
            Self::Binary(instr) => instr.visit_values_mut(visitor),
            Self::Compare(instr) => instr.visit_values_mut(visitor),
            Self::Demote(instr) => instr.visit_values_mut(visitor),
            Self::Promote(instr) => instr.visit_values_mut(visitor),
            Self::FloatToInt(instr) => instr.visit_values_mut(visitor),
        }
    }
}

macro_rules! impl_from_float_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Float(crate::instr::FloatInstr::from(instr))
                }
            }
        )*
    };
}
impl_from_float_instr_for_instr! {
    CompareFloatInstr,
    DemoteFloatInstr,
    PromoteFloatInstr,
    FloatToIntInstr,
    UnaryFloatInstr,
    BinaryFloatInstr,
}
