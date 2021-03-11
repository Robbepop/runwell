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
mod select;
mod terminal;

use core::fmt;

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
    select::MatchSelectInstr,
    terminal::{
        BranchInstr,
        BranchTableInstr,
        IfThenElseInstr,
        ReturnInstr,
        TailCallIndirectInstr,
        TailCallInstr,
        TerminalInstr,
    },
};
use super::primitive::Value;
use crate::{
    DisplayEdge,
    DisplayInstruction,
    Indent,
    VisitValues,
    VisitValuesMut,
};
use derive_more::From;
use smallvec::SmallVec;

/// A space-optimized vector containing values.
///
/// This has the exact amount of inline elements required for the
/// small vector to have the same stack size as the `Vec<Value>` type.
type SmallValueVec = SmallVec<[Value; 4]>;

/// An SSA instruction from the Runwell IR.
#[derive(Debug, From, PartialEq, Eq, Hash, Clone)]
pub enum Instruction {
    Call(CallInstr),
    CallIndirect(CallIndirectInstr),
    Const(ConstInstr),
    MemoryGrow(MemoryGrowInstr),
    MemorySize(MemorySizeInstr),
    HeapAddr(HeapAddrInstr),
    Load(LoadInstr),
    Store(StoreInstr),
    Select(MatchSelectInstr),
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

impl DisplayInstruction for Instruction {
    fn display_instruction(
        &self,
        f: &mut dyn fmt::Write,
        indent: Indent,
        displayer: &dyn DisplayEdge,
    ) -> fmt::Result {
        match self {
            Self::Call(instr) => write!(f, "{}", instr)?,
            Self::CallIndirect(instr) => write!(f, "{}", instr)?,
            Self::Const(instr) => write!(f, "{}", instr)?,
            Self::MemoryGrow(instr) => write!(f, "{}", instr)?,
            Self::MemorySize(instr) => write!(f, "{}", instr)?,
            Self::HeapAddr(instr) => write!(f, "{}", instr)?,
            Self::Load(instr) => write!(f, "{}", instr)?,
            Self::Store(instr) => write!(f, "{}", instr)?,
            Self::Select(instr) => {
                instr.display_instruction(f, indent, displayer)?
            }
            Self::Reinterpret(instr) => write!(f, "{}", instr)?,
            Self::Terminal(instr) => {
                instr.display_instruction(f, indent, displayer)?
            }
            Self::Int(instr) => write!(f, "{}", instr)?,
            Self::Float(instr) => write!(f, "{}", instr)?,
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_of_instruction_is_kept_small() {
        use core::mem::size_of;
        // Ideally we keep the size of generic instructions as small as possible.
        assert_eq!(size_of::<Instruction>(), 56);
        // Also assert the sizes of the biggest known concrete instructions.
        assert_eq!(size_of::<TerminalInstr>(), 40);
        assert_eq!(size_of::<BranchTableInstr>(), 32);
        assert_eq!(size_of::<CallIndirectInstr>(), 32);
        assert_eq!(size_of::<MatchSelectInstr>(), 48);
    }
}
