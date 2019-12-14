// Copyright 2019 Robin Freyler
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

//! Intermediate representation of a WebAssembly (Wasm) module.

use derive_more::From;

mod basicblock;
mod int;
mod memory;
pub mod source;
mod terminal;
mod utils;

/// Operations of the intermediate representation.
pub mod op {
    /// Opertion kinds.
    pub mod kind {
        pub use super::super::int::kinds::*;
    }
    /// Extra structs and helpers used by some operations.
    pub mod extra {
        pub use super::super::memory::{AllocaOpArrayParams, PhiOpOrigin};
    }
    pub use super::{
        int::{
            AndOp,
            IntAddOp,
            IntCompareOp,
            IntMulOp,
            IntSdivOp,
            IntSremOp,
            IntSubOp,
            IntTruncateOp,
            IntUdivOp,
            IntUremOp,
            LeadingZerosOp,
            OrOp,
            PopcountOp,
            RotlOp,
            RotrOp,
            ShlOp,
            SignExtendOp,
            SshrOp,
            TrailingZerosOp,
            UshrOp,
            XorOp,
            ZeroExtendOp,
        },
        memory::{AllocaOp, LoadOp, PhiOp, StoreOp},
        terminal::{BranchOp, BranchTableOp, IteOp, ReturnOp},
    };
}

pub use self::{
    basicblock::BasicBlock,
    int::{GenericIntBinaryOp, GenericIntUnaryOp, IntOp},
    terminal::TerminalOp,
    utils::{FloatType, GlobalVar, IntType, Label, LocalVar, PtrType, Type},
};

pub(crate) mod sealed {
    /// Used to seal certain generic operations.
    pub trait Sealed {}
}

/// Any operation.
///
/// Converted directly from Wasm bytecode into SSA form.
#[derive(From)]
pub enum Op {
    Alloca(op::AllocaOp),
    Load(op::LoadOp),
    Store(op::StoreOp),
    Phi(op::PhiOp),
    Int(IntOp),
    Terminal(TerminalOp),
}
