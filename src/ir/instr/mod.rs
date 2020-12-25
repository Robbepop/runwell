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
mod float;
mod int;
mod memory;
mod phi;
mod select;
mod terminal;

pub use self::{
    call::{CallIndirectInstr, CallInstr},
    constant::ConstInstr,
    float::{
        AbsInstr,
        CeilInstr,
        FloatCompareInstr,
        FloatCompareOp,
        FloorInstr,
        NearestInstr,
        NegInstr,
        SqrtInstr,
        TruncInstr,
        UnaryFloatInstr,
        DemoteInstr,
        PromoteInstr,
        BinaryFloatInstr,
        FaddInstr,
        FcopysignInstr,
        FdivInstr,
        FmaxInstr,
        FminInstr,
        FmulInstr,
        FsubInstr,
    },
    int::{
        AddInstr,
        AndInstr,
        BinaryIntInstr,
        IntCompareInstr,
        IntCompareOp,
        LeadingZerosInstr,
        MulInstr,
        OrInstr,
        PopCountInstr,
        RotlInstr,
        RotrInstr,
        SdivInstr,
        ShiftInstr,
        ShlInstr,
        SignExtendInstr,
        SremInstr,
        SshlrInstr,
        SubInstr,
        TrailingZerosInstr,
        TruncateInstr,
        UdivInstr,
        UnaryIntInstr,
        UremInstr,
        UshlrInstr,
        XorInstr,
        ZeroExtendInstr,
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
    // Generic Instructions
    Call(CallInstr),
    CallIndirect(CallIndirectInstr),
    Const(ConstInstr),
    MemoryGrow(MemoryGrowInstr),
    MemorySize(MemorySizeInstr),
    Phi(PhiInstr),
    Load(LoadInstr),
    Store(StoreInstr),
    Select(SelectInstr),
    Terminal(TerminalInstr),

    // Integer Instructions
    Add(AddInstr),
    And(AndInstr),
    Compare(IntCompareInstr),
    LeadingZeros(LeadingZerosInstr),
    Mul(MulInstr),
    Or(OrInstr),
    PopCount(PopCountInstr),
    Rotl(RotlInstr),
    Rotr(RotrInstr),
    Sdiv(SdivInstr),
    Shl(ShlInstr),
    SignExtend(SignExtendInstr),
    Srem(SremInstr),
    Sshlr(SshlrInstr),
    Sub(SubInstr),
    TrailingZeros(TrailingZerosInstr),
    Truncate(TruncateInstr),
    Udiv(UdivInstr),
    Urem(UremInstr),
    Ushlr(UshlrInstr),
    Xor(XorInstr),
    ZeroExtend(ZeroExtendInstr),
}
