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
mod memory;
mod phi;
mod select;
mod terminal;
mod utils;

use crate::ir::Binding;

#[doc(inline)]
pub use self::{
    call::{CallIndirectOp, CallOp},
    constant::ConstOp,
    convert::{SignExtendOp, TruncateOp, ZeroExtendOp},
    destination::DestinationId,
    int::{GenericBinaryIntOp, GenericUnaryIntOp, IntOp},
    load_store::{LoadOp, LocalOp, StoreOp},
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

    }
}
