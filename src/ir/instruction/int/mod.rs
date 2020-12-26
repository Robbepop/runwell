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
mod shift;
mod unary;

pub use self::{
    binary::{
        BinaryIntInstr,
        IaddInstr,
        IandInstr,
        ImulInstr,
        IorInstr,
        IsubInstr,
        IxorInstr,
        SdivInstr,
        SremInstr,
        UdivInstr,
        UremInstr,
    },
    icmp::{IcompareInstr, IcompareOp},
    iconv::{
        ItruncateInstr,
        SextendInstr,
        SintToFloatInstr,
        UextendInstr,
        UintToFloatInstr,
    },
    shift::{
        IrotlInstr,
        IrotrInstr,
        ShiftInstr,
        ShlInstr,
        SshlrInstr,
        UshlrInstr,
    },
    unary::{
        IleadingZerosInstr,
        IpopCountInstr,
        ItrailingZerosInstr,
        UnaryIntInstr,
    },
};
use derive_more::{Display, From};

/// An SSA integer instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq)]
pub enum IntInstr {
    Add(IaddInstr),
    And(IandInstr),
    Compare(IcompareInstr),
    LeadingZeros(IleadingZerosInstr),
    Mul(ImulInstr),
    Or(IorInstr),
    PopCount(IpopCountInstr),
    Rotl(IrotlInstr),
    Rotr(IrotrInstr),
    Sdiv(SdivInstr),
    Shl(ShlInstr),
    SignExtend(SextendInstr),
    SintToFloat(SintToFloatInstr),
    Srem(SremInstr),
    Sshlr(SshlrInstr),
    Sub(IsubInstr),
    TrailingZeros(ItrailingZerosInstr),
    Truncate(ItruncateInstr),
    Udiv(UdivInstr),
    UintToFloat(UintToFloatInstr),
    Urem(UremInstr),
    Ushlr(UshlrInstr),
    Xor(IxorInstr),
    ZeroExtend(UextendInstr),
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
    IaddInstr,
    IandInstr,
    IcompareInstr,
    IleadingZerosInstr,
    ImulInstr,
    IorInstr,
    IpopCountInstr,
    IrotlInstr,
    IrotrInstr,
    SdivInstr,
    ShlInstr,
    SextendInstr,
    SintToFloatInstr,
    SremInstr,
    SshlrInstr,
    IsubInstr,
    ItrailingZerosInstr,
    ItruncateInstr,
    UdivInstr,
    UintToFloatInstr,
    UremInstr,
    UshlrInstr,
    IxorInstr,
    UextendInstr,
}
