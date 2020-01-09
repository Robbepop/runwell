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
    ir,
    ir::{Binding, BlockId, CallParam},
    parse::{FunctionId, Type},
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
#[derive(From, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TerminalOp {
    #[from(ignore)] Unreachable,
    Return(ReturnOp),
    Branch(BranchOp),
    Ite(IteOp),
    BranchTable(BranchTableOp),
    CallTail(CallTailOp),
}

/// Unconditionally branches to the given block.
///
/// Branches to blocks are always local to the current function.
///
/// ```no_compile
/// br block 2
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BranchOp {
    /// The label to branch to.
    id: BlockId,
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct IteOp {
    /// The condition. Should gracefully evaluate to `1` (true) or `0` (false).
    cond: Binding,
    /// The branch taken if `cond` evaluates to `!= 0`.
    then_block: BlockId,
    /// The branch taken if `cond` evaluates to `== 0`.
    else_block: BlockId,
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BranchTableOp {
    /// The source value ID.
    src: Binding,
    /// The default branch block.
    default: BlockId,
    /// The blocks used for branches.
    locs: Vec<BlockId>,
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReturnOp {
    /// The type of the return value.
    ty: Type,
    /// The optional return type.
    ///
    /// Has to match the return type of the enclosing function.
    value: Option<Binding>,
}

impl ReturnOp {
    /// Creates a new return operator.
    pub fn new<T>(ty: Type, value: T) -> Self
    where
        T: Into<Option<Binding>>,
    {
        Self {
            ty,
            value: value.into(),
        }
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CallTailOp {
    /// The tail-called function ID.
    id: FunctionId,
    /// The function call parameters.
    params: Vec<CallParam>,
}

impl From<BranchOp> for ir::Operator {
    fn from(op: BranchOp) -> Self {
        ir::Operator::Terminal(TerminalOp::from(op))
    }
}

impl From<IteOp> for ir::Operator {
    fn from(op: IteOp) -> Self {
        ir::Operator::Terminal(TerminalOp::from(op))
    }
}

impl From<BranchTableOp> for ir::Operator {
    fn from(op: BranchTableOp) -> Self {
        ir::Operator::Terminal(TerminalOp::from(op))
    }
}

impl From<ReturnOp> for ir::Operator {
    fn from(op: ReturnOp) -> Self {
        ir::Operator::Terminal(TerminalOp::from(op))
    }
}

impl From<CallTailOp> for ir::Operator {
    fn from(op: CallTailOp) -> Self {
        ir::Operator::Terminal(TerminalOp::from(op))
    }
}
