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
        BinaryFloatOp,
        CompareFloatInstr,
        CompareFloatOp,
        DemoteFloatInstr,
        FloatInstr,
        FloatToIntInstr,
        PromoteFloatInstr,
        UnaryFloatInstr,
        UnaryFloatOp,
    },
    int::{
        BinaryIntInstr,
        BinaryIntOp,
        CompareIntInstr,
        CompareIntOp,
        ExtendIntInstr,
        IntInstr,
        IntToFloatInstr,
        TruncateIntInstr,
        UnaryIntInstr,
        UnaryIntOp,
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
    terminal::{
        BranchInstr,
        BranchTableInstr,
        IfThenElseInstr,
        ReturnInstr,
        TerminalInstr,
    },
};
use derive_more::{Display, From};

/// An SSA instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, Hash)]
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
    Float(FloatInstr),
}

impl Instruction {
    /// Returns `true` if the instruction terminates a basic block.
    pub fn is_terminal(&self) -> bool {
        matches!(self, Self::Terminal(_))
    }

    /// Returns `true` if the instruction is a ϕ-instruction.
    pub fn is_phi(&self) -> bool {
        matches!(self, Self::Phi(_))
    }
}
