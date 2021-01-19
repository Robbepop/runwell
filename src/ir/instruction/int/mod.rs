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
mod icmp;
mod iconv;
mod unary;

pub use self::{
    binary::{BinaryIntInstr, BinaryIntOp},
    icmp::{CompareIntInstr, CompareIntOp},
    iconv::{ExtendIntInstr, IntToFloatInstr, TruncateIntInstr},
    unary::{UnaryIntInstr, UnaryIntOp},
};
use derive_more::{Display, From};

/// An SSA integer instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntInstr {
    Binary(BinaryIntInstr),
    Unary(UnaryIntInstr),
    Compare(CompareIntInstr),
    Extend(ExtendIntInstr),
    IntToFloat(IntToFloatInstr),
    Truncate(TruncateIntInstr),
}

macro_rules! impl_from_int_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::ir::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Int(crate::ir::instr::IntInstr::from(instr))
                }
            }
        )*
    };
}
impl_from_int_instr_for_instr! {
    BinaryIntInstr,
    UnaryIntInstr,
    CompareIntInstr,
    TruncateIntInstr,
    IntToFloatInstr,
    ExtendIntInstr,
}
