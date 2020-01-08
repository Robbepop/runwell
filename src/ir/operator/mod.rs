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

//! Operators of the `runwell` IR.

mod call;
mod constant;
mod convert;
mod destination;
pub mod int;
mod load_store;
mod local_global;
mod memory;
mod phi;
mod select;
mod terminal;
mod utils;

use crate::ir::ValueId;

#[doc(inline)]
pub use self::{
    call::{CallIndirectOp, CallOp},
    constant::ConstOp,
    convert::{SignExtendOp, TruncateOp, ZeroExtendOp},
    destination::DestinationId,
    int::{GenericBinaryIntOp, GenericUnaryIntOp, IntOp},
    load_store::{LoadOp, StoreOp},
    local_global::{GetOp, LocalOp, SetOp},
    memory::{MemoryGrowOp, MemorySizeOp},
    phi::{PhiOp, PhiOpOrigin},
    select::SelectOp,
    terminal::{
        BranchOp,
        BranchTableOp,
        CallTailOp,
        IteOp,
        ReturnOp,
        TerminalOp,
    },
    utils::CallParam,
};
use derive_more::From;

/// Any operation.
///
/// Converted directly from Wasm bytecode into SSA form.
///
/// # Note
///
/// Due to runtime guarantees of the `runwell` JIT compiler the SSA IR is
/// generally not guaranteed to be in minimal or pruned SSA form.
/// Even if optimizations are turned on they are not guaranteed to compute
/// completely to guarantee the runtime behaviour of the compilation.
#[derive(Debug, From, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operator {
    Const(ConstOp),
    Local(LocalOp),
    Get(GetOp),
    Set(SetOp),
    Load(LoadOp),
    Store(StoreOp),
    Phi(PhiOp),
    MemoryGrow(MemoryGrowOp),
    MemorySize(MemorySizeOp),
    Call(CallOp),
    CallIndirect(CallIndirectOp),
    Truncate(TruncateOp),
    ZeroExtend(ZeroExtendOp),
    Select(SelectOp),
    SignExtend(SignExtendOp),
    Int(IntOp),
    Terminal(TerminalOp),
}

impl DestinationId for Operator {
    fn destination_id(&self) -> Option<ValueId> {
        match self {
            Self::Const(op) => op.destination_id(),
            Self::Local(op) => op.destination_id(),
            Self::Get(op) => op.destination_id(),
            Self::Set(op) => op.destination_id(),
            Self::Load(op) => op.destination_id(),
            Self::Store(op) => op.destination_id(),
            Self::Phi(op) => op.destination_id(),
            Self::MemoryGrow(op) => op.destination_id(),
            Self::MemorySize(op) => op.destination_id(),
            Self::Call(op) => op.destination_id(),
            Self::CallIndirect(op) => op.destination_id(),
            Self::Truncate(op) => op.destination_id(),
            Self::ZeroExtend(op) => op.destination_id(),
            Self::Select(op) => op.destination_id(),
            Self::SignExtend(op) => op.destination_id(),
            Self::Int(op) => op.destination_id(),
            Self::Terminal(op) => op.destination_id(),
        }
    }
}
