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

use crate::primitive::Instr;
use ir::primitive::{Block, Edge, Value};

/// A user of an SSA value.
///
/// This can be either an instruction or a branching edge.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum ValueUser {
    Instr(Instr),
    Param(Value),
    Edge(Edge),
}

/// The definition site of the SSA value.
///
/// Every SSA value has a definition site that is either a function input
/// a block parameter or the nth returned value of an instruction.
#[derive(Debug, Copy, Clone)]
pub enum ValueDefinition {
    /// The value is defined as the nth parameter of the basic block.
    Param(Block, u32),
    /// The value is associated to the nth output of the instruction.
    Instr(Instr, u32),
}
