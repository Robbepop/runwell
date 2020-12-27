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
    binary::{
        BinaryFloatInstr,
        FaddInstr,
        FcopysignInstr,
        FdivInstr,
        FmaxInstr,
        FminInstr,
        FmulInstr,
        FsubInstr,
    },
    fcmp::{FcompareInstr, FcompareOp},
    fconv::{FdemoteInstr, FpromoteInstr, FtoSintInstr, FtoUintInstr},
    unary::{
        FabsInstr,
        FceilInstr,
        FfloorInstr,
        FnearestInstr,
        FnegInstr,
        FsqrtInstr,
        FtruncateInstr,
        UnaryFloatInstr,
    },
};
use derive_more::{Display, From};

/// An SSA floating point number instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatInstr {
    Abs(FabsInstr),
    Add(FaddInstr),
    Ceil(FceilInstr),
    Compare(FcompareInstr),
    Copysign(FcopysignInstr),
    Demote(FdemoteInstr),
    Div(FdivInstr),
    Floor(FfloorInstr),
    Max(FmaxInstr),
    Min(FminInstr),
    Mul(FmulInstr),
    Nearest(FnearestInstr),
    Neg(FnegInstr),
    Promote(FpromoteInstr),
    Sqrt(FsqrtInstr),
    Sub(FsubInstr),
    ToSint(FtoSintInstr),
    ToUint(FtoUintInstr),
    Truncate(FtruncateInstr),
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
    FabsInstr,
    FaddInstr,
    FceilInstr,
    FcompareInstr,
    FcopysignInstr,
    FdemoteInstr,
    FdivInstr,
    FfloorInstr,
    FmaxInstr,
    FminInstr,
    FmulInstr,
    FnearestInstr,
    FnegInstr,
    FpromoteInstr,
    FsqrtInstr,
    FsubInstr,
    FtoSintInstr,
    FtoUintInstr,
    FtruncateInstr,
}
