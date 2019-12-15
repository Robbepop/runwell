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

use crate::ir::{
    source::{I32Source, Source, Value},
    Label,
};
use derive_more::From;
use crate::maybe_std::prelude::*;

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
    Return(ReturnOp),
    Branch(BranchOp),
    Ite(IteOp),
    BranchTable(BranchTableOp),
    Unreachable,
}

/// Unconditionally branches to the given label.
///
/// Branches are function local and can only branch into a block or labelled
/// entity defined within the same function.
pub struct BranchOp {
    /// The label to branch to.
    label: Label,
}

/// An if-then-else branch instruction.
///
/// Jumps to `then_br` if `cond` evaluates to `!= 0` or to `else_br` otherwise.
pub struct IteOp {
    /// The condition. Should gracefully evaluate to `1` (true) or `0` (false).
    cond: I32Source,
    /// The branch taken if `cond` evaluates to `!= 0`.
    then_br: Label,
    /// The branch taken if `cond` evaluates to `== 0`.
    else_br: Label,
}

/// A branch table to jump to either of the destinations given `src`.
///
/// # Note
///
/// If `src` doesn't match with either destination a jump to `default` is taken.
pub struct BranchTableOp {
    src: Source,
    default: Label,
    locs: Vec<Label>,
}

/// Returns back to the caller from the current function.
///
/// Optionally carries a return value.
/// Returns `()` if nothing specified.
pub struct ReturnOp {
    /// The optional return type.
    ///
    /// Has to match the return type of the enclosing function.
    value: Option<Value>,
}
