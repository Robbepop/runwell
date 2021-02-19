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
        ShiftIntInstr,
        ShiftIntOp,
        TruncateIntInstr,
        UnaryIntInstr,
        UnaryIntOp,
    },
    memory::{
        HeapAddrInstr,
        ImmU32,
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
        TailCallInstr,
        TerminalInstr,
    },
};
use super::primitive::Value;
use crate::{primitive::Block, VisitValues, VisitValuesMut};
use derive_more::{Display, From};
use smallvec::SmallVec;

/// A space-optimized vector containing values.
///
/// This has the exact amount of inline elements required for the
/// small vector to have the same stack size as the `Vec<Value>` type.
type SmallValueVec = SmallVec<[Value; 4]>;

/// A space-optimized vector containing basic blocks.
///
/// This has the exact amount of inline elements required for the
/// small vector to have the same stack size as the `Vec<Block>` type.
type SmallBlockVec = SmallVec<[Block; 4]>;

/// An SSA instruction from the Runwell IR.
#[derive(Debug, Display, From, PartialEq, Eq, Hash, Clone)]
pub enum Instruction {
    Call(CallInstr),
    CallIndirect(CallIndirectInstr),
    Const(ConstInstr),
    MemoryGrow(MemoryGrowInstr),
    MemorySize(MemorySizeInstr),
    HeapAddr(HeapAddrInstr),
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

impl VisitValues for Instruction {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        match self {
            Self::Call(instr) => instr.visit_values(visitor),
            Self::CallIndirect(instr) => instr.visit_values(visitor),
            Self::Const(instr) => instr.visit_values(visitor),
            Self::MemoryGrow(instr) => instr.visit_values(visitor),
            Self::MemorySize(__instr) => (),
            Self::Phi(instr) => instr.visit_values(visitor),
            Self::HeapAddr(instr) => instr.visit_values(visitor),
            Self::Load(instr) => instr.visit_values(visitor),
            Self::Store(instr) => instr.visit_values(visitor),
            Self::Select(instr) => instr.visit_values(visitor),
            Self::Reinterpret(instr) => instr.visit_values(visitor),
            Self::Terminal(instr) => instr.visit_values(visitor),
            Self::Int(instr) => instr.visit_values(visitor),
            Self::Float(instr) => instr.visit_values(visitor),
        }
    }
}

impl VisitValuesMut for Instruction {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        match self {
            Self::Call(instr) => instr.visit_values_mut(visitor),
            Self::CallIndirect(instr) => instr.visit_values_mut(visitor),
            Self::Const(instr) => instr.visit_values_mut(visitor),
            Self::MemoryGrow(instr) => instr.visit_values_mut(visitor),
            Self::MemorySize(__instr) => (),
            Self::Phi(instr) => instr.visit_values_mut(visitor),
            Self::HeapAddr(instr) => instr.visit_values_mut(visitor),
            Self::Load(instr) => instr.visit_values_mut(visitor),
            Self::Store(instr) => instr.visit_values_mut(visitor),
            Self::Select(instr) => instr.visit_values_mut(visitor),
            Self::Reinterpret(instr) => instr.visit_values_mut(visitor),
            Self::Terminal(instr) => instr.visit_values_mut(visitor),
            Self::Int(instr) => instr.visit_values_mut(visitor),
            Self::Float(instr) => instr.visit_values_mut(visitor),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_of_instruction_is_kept_small() {
        use core::mem::size_of;
        // Ideally we keep the size of generic instructions as small as possible.
        assert_eq!(size_of::<Instruction>(), 48);
        // Also assert the sizes of the biggest known concrete instructions.
        assert_eq!(size_of::<TerminalInstr>(), 40);
        assert_eq!(size_of::<BranchTableInstr>(), 32);
        assert_eq!(size_of::<PhiInstr>(), 24);
        assert_eq!(size_of::<CallIndirectInstr>(), 32);
    }
}
