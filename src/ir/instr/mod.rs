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

mod call;
mod constant;
mod conv;
mod float;
mod int;
mod memory;
mod phi;
mod select;
mod terminal;

pub use self::{
    call::{CallIndirectInstr, CallInstr},
    constant::ConstInstr,
    conv::ReinterpretInstr,
    float::{
        BinaryFloatInstr,
        FabsInstr,
        FaddInstr,
        FceilInstr,
        FcompareInstr,
        FcompareOp,
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
        FtruncateInstr,
        UnaryFloatInstr,
    },
    int::{
        BinaryIntInstr,
        IaddInstr,
        IandInstr,
        IcompareInstr,
        IcompareOp,
        IleadingZerosInstr,
        ImulInstr,
        IorInstr,
        IpopCountInstr,
        IrotlInstr,
        IrotrInstr,
        IsubInstr,
        ItrailingZerosInstr,
        ItruncateInstr,
        IxorInstr,
        SdivInstr,
        SextendInstr,
        ShiftInstr,
        ShlInstr,
        SremInstr,
        SshlrInstr,
        UdivInstr,
        UextendInstr,
        UnaryIntInstr,
        UremInstr,
        UshlrInstr,
    },
    memory::{
        Alignment,
        LoadInstr,
        MemoryGrowInstr,
        MemorySizeInstr,
        StoreInstr,
    },
    phi::PhiInstr,
    select::SelectInstr,
    terminal::TerminalInstr,
};
use derive_more::{Display, From};

/// An SSA instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq)]
pub enum Instruction {
    Call(CallInstr),
    CallIndirect(CallIndirectInstr),
    Const(ConstInstr),
    MemoryGrow(MemoryGrowInstr),
    MemorySize(MemorySizeInstr),
    Phi(PhiInstr),
    Load(LoadInstr),
    Store(StoreInstr),
    Select(SelectInstr),
    Reinterpret(ReinterpretInstr),
    Terminal(TerminalInstr),
    Int(IntInstr),
}

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
    Srem(SremInstr),
    Sshlr(SshlrInstr),
    Sub(IsubInstr),
    TrailingZeros(ItrailingZerosInstr),
    Truncate(ItruncateInstr),
    Udiv(UdivInstr),
    Urem(UremInstr),
    Ushlr(UshlrInstr),
    Xor(IxorInstr),
    ZeroExtend(UextendInstr),
}

/// An SSA floating point number instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq)]
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
    Truncate(FtruncateInstr),
}
