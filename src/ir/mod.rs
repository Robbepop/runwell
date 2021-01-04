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

mod bb;
mod builder;
mod error;
mod instruction;
mod primitives;
mod value;
mod wasm;

pub use self::{
    bb::BasicBlockId,
    error::IrError,
    builder::FunctionBuilderError,
    instruction::Alignment,
    primitives::{Const, FloatConst, FloatType, IntConst, IntType, Type},
    value::Value,
    wasm::{translate_wasm, WasmError},
};
use self::{
    builder::{Instr, Variable},
    value::ValueGen,
};

/// All Runwell IR SSA instructions.
pub mod instr {
    /// The operands for some of the instructions.
    pub mod operands {
        #[doc(inline)]
        pub use super::super::instruction::{FcompareOp, IcompareOp};
    }
    /// The base types for all the alias instruction types.
    pub mod base {
        #[doc(inline)]
        pub use super::super::instruction::{
            BinaryFloatInstr,
            BinaryIntInstr,
            UnaryFloatInstr,
            UnaryIntInstr,
        };
    }
    #[doc(inline)]
    pub use super::instruction::{
        CallIndirectInstr,
        CallInstr,
        ConstInstr,
        FabsInstr,
        FaddInstr,
        FceilInstr,
        FcompareInstr,
        FcopysignInstr,
        FdemoteInstr,
        FdivInstr,
        FfloorInstr,
        FloatInstr,
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
        IaddInstr,
        IandInstr,
        IcompareInstr,
        IleadingZerosInstr,
        ImulInstr,
        Instruction,
        IntInstr,
        IorInstr,
        IpopCountInstr,
        IrotlInstr,
        IrotrInstr,
        IshlInstr,
        IsubInstr,
        ItrailingZerosInstr,
        ItruncateInstr,
        IxorInstr,
        LoadInstr,
        MemoryGrowInstr,
        MemorySizeInstr,
        PhiInstr,
        ReinterpretInstr,
        SdivInstr,
        SelectInstr,
        SextendInstr,
        ShiftInstr,
        SremInstr,
        SshlrInstr,
        StoreInstr,
        TerminalInstr,
        UdivInstr,
        UextendInstr,
        UremInstr,
        UshlrInstr,
    };
}
