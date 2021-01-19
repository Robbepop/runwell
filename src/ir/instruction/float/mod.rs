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

mod binary;
mod fcmp;
mod fconv;
mod unary;

pub use self::{
    binary::{BinaryFloatInstr, BinaryFloatOp},
    fcmp::{CompareFloatInstr, CompareFloatOp},
    fconv::{DemoteFloatInstr, FloatToIntInstr, PromoteFloatInstr},
    unary::{UnaryFloatInstr, UnaryFloatOp},
};
use derive_more::{Display, From};

/// An SSA floating point number instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatInstr {
    Unary(UnaryFloatInstr),
    Binary(BinaryFloatInstr),
    Compare(CompareFloatInstr),
    Demote(DemoteFloatInstr),
    Promote(PromoteFloatInstr),
    FloatToInt(FloatToIntInstr),
}

macro_rules! impl_from_float_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::ir::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Float(crate::ir::instr::FloatInstr::from(instr))
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
