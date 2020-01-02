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

use crate::{
    ir::{operator::DestinationId, BlockId, CallParam, ValueId},
    parse::FunctionId,
};
use derive_more::From;

/// Any terminal operation.
///
/// Used to jump to a new labelled entitiy,
/// return back to the caller of a function,
/// or to end the execution.
///
/// # Note
///
/// A basic block requires a terminal instruction at its last operation.
#[derive(From)]
pub enum TerminalOp {
    Unreachable,
    Return(ReturnOp),
    Branch(BranchOp),
    Ite(IteOp),
    BranchTable(BranchTableOp),
    CallTail(CallTailOp),
}

impl DestinationId for TerminalOp {
    fn destination_id(&self) -> Option<ValueId> {
        // By definition terminal operations cannot have bindings.
        None
    }
}

/// Unconditionally branches to the given block.
///
/// Branches to blocks are always local to the current function.
///
/// ```no_compile
/// br block 2
/// ```
pub struct BranchOp {
    /// The label to branch to.
    id: BlockId,
}

impl DestinationId for BranchOp {
    fn destination_id(&self) -> Option<ValueId> {
        // By definition terminal operations cannot have bindings.
        None
    }
}

/// An if-then-else branch instruction.
///
/// Jumps to `then_br` if `cond` evaluates to `!= 0` or to `else_br` otherwise.
///
/// # Examples
///
/// Without returning a value:
///
/// ```no_compile
/// ite %1 then block %0, else block %2
/// ```
pub struct IteOp {
    /// The condition. Should gracefully evaluate to `1` (true) or `0` (false).
    cond: ValueId,
    /// The branch taken if `cond` evaluates to `!= 0`.
    then_block: BlockId,
    /// The branch taken if `cond` evaluates to `== 0`.
    else_block: BlockId,
}

impl DestinationId for IteOp {
    fn destination_id(&self) -> Option<ValueId> {
        // By definition terminal operations cannot have bindings.
        None
    }
}

/// A branch table to jump to either of the destinations given `src`.
///
/// # Note
///
/// If `src` doesn't match with either destination a jump to `default` is taken.
///
/// # Examples
///
/// Without returning a value:
///
/// ```no_compile
/// brtable default block 0 [block 2, block 0, block 1]]
/// ```
pub struct BranchTableOp {
    /// The source value ID.
    src: ValueId,
    /// The default branch block.
    default: BlockId,
    /// The blocks used for branches.
    locs: Vec<BlockId>,
}

impl DestinationId for BranchTableOp {
    fn destination_id(&self) -> Option<ValueId> {
        // By definition terminal operations cannot have bindings.
        None
    }
}

/// Returns back to the caller from the current function.
///
/// Optionally carries a return value.
/// Returns `()` if nothing specified.
///
/// # Examples
///
/// Without returning a value:
///
/// ```no_compile
/// return
/// ```
///
/// Returning a value:
///
/// ```no_compile
/// return %1
/// ```
pub struct ReturnOp {
    /// The optional return type.
    ///
    /// Has to match the return type of the enclosing function.
    value: Option<ValueId>,
}

impl DestinationId for ReturnOp {
    fn destination_id(&self) -> Option<ValueId> {
        // By definition terminal operations cannot have bindings.
        None
    }
}

/// Tail-calls the function identified by the ID.
///
/// # Note
///
/// Useful to optimize certain recursive call schemes.
///
/// # Examples
///
/// Tail calls the function identified by `120` with parameters `%1` of type
/// `i32`, `%2` of type `i64` and `%4` of type `i32`.
///
/// ```no_compile
/// call.tail fn 120 params [ i32 %1, i64 %2, i32 %4 ]
/// ```
pub struct CallTailOp {
    /// The tail-called function ID.
    id: FunctionId,
    /// The function call parameters.
    params: Vec<CallParam>,
}

impl DestinationId for CallTailOp {
    fn destination_id(&self) -> Option<ValueId> {
        // By definition terminal operations cannot have bindings.
        None
    }
}
