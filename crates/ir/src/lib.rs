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

//! Runwell IR data structures, SSA builder and IR interpreter.

#![forbid(unsafe_code)]

mod display;
mod edge_visitor;
mod instruction;
pub mod primitive;
mod value_visitor;

pub use self::{
    display::{DisplayEdge, DisplayInstruction, Indent},
    edge_visitor::{VisitEdges, VisitEdgesMut},
    instruction::ImmU32,
    value_visitor::{VisitValues, VisitValuesMut},
};

#[cfg(test)]
use self::display::DebugDisplayEdge;

/// All Runwell IR SSA instructions.
pub mod instr {
    /// Utility types to construct or interact with some instructions.
    pub mod utils {
        #[doc(inline)]
        pub use super::super::instruction::{
            MatchBranchInstrBuilder,
            MatchSelectInstrBuilder,
            MatchSelectResultsIter,
        };
    }
    /// The operands for some instructions.
    pub mod operands {
        #[doc(inline)]
        pub use super::super::instruction::{
            BinaryFloatOp,
            BinaryIntOp,
            CompareFloatOp,
            CompareIntOp,
            ShiftIntOp,
            UnaryFloatOp,
            UnaryIntOp,
        };
    }
    #[doc(inline)]
    pub use super::instruction::{
        BinaryFloatInstr,
        BinaryIntInstr,
        BranchInstr,
        CallIndirectInstr,
        CallInstr,
        CompareFloatInstr,
        CompareIntInstr,
        ConstInstr,
        DemoteFloatInstr,
        ExtendIntInstr,
        FloatInstr,
        FloatToIntInstr,
        HeapAddrInstr,
        IfThenElseInstr,
        Instruction,
        IntInstr,
        IntToFloatInstr,
        LoadInstr,
        MatchBranchInstr,
        MatchSelectInstr,
        MemoryGrowInstr,
        MemorySizeInstr,
        PromoteFloatInstr,
        ReinterpretInstr,
        ReturnInstr,
        ShiftIntInstr,
        StoreInstr,
        TailCallIndirectInstr,
        TailCallInstr,
        TerminalInstr,
        TruncateIntInstr,
        UnaryFloatInstr,
        UnaryIntInstr,
    };
}
