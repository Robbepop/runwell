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

use super::{CallIndirectInstr, CallInstr};
use crate::{
    primitive::{Edge, Func, FuncType, Table, Value},
    DisplayEdge,
    DisplayInstruction,
    Indent,
    VisitValues,
    VisitValuesMut,
};
use core::fmt::{self, Display};
use derive_more::{Display, From};
use smallvec::SmallVec;

/// A terminal SSA instruction.
///
/// Every basic block is required to have a terminal instruction
/// as its last instruction.
#[derive(Debug, From, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TerminalInstr {
    Trap,
    Return(ReturnInstr),
    Br(BranchInstr),
    Ite(IfThenElseInstr),
    TailCall(TailCallInstr),
    TailCallIndirect(TailCallIndirectInstr),
    BranchTable(BranchTableInstr),
}

impl VisitValues for TerminalInstr {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        match self {
            Self::Trap => (),
            Self::Return(instr) => instr.visit_values(visitor),
            Self::Br(_instr) => (),
            Self::Ite(instr) => instr.visit_values(visitor),
            Self::TailCall(instr) => instr.visit_values(visitor),
            Self::TailCallIndirect(instr) => instr.visit_values(visitor),
            Self::BranchTable(instr) => instr.visit_values(visitor),
        }
    }
}

impl VisitValuesMut for TerminalInstr {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        match self {
            Self::Trap => (),
            Self::Return(instr) => instr.visit_values_mut(visitor),
            Self::Br(_instr) => (),
            Self::Ite(instr) => instr.visit_values_mut(visitor),
            Self::TailCall(instr) => instr.visit_values_mut(visitor),
            Self::TailCallIndirect(instr) => instr.visit_values_mut(visitor),
            Self::BranchTable(instr) => instr.visit_values_mut(visitor),
        }
    }
}

impl DisplayInstruction for TerminalInstr {
    fn display_instruction(
        &self,
        f: &mut fmt::Formatter,
        indent: Indent,
        displayer: &dyn DisplayEdge,
    ) -> fmt::Result {
        match self {
            TerminalInstr::Trap => write!(f, "trap")?,
            TerminalInstr::Return(instr) => write!(f, "{}", instr)?,
            TerminalInstr::Br(instr) => {
                instr.display_instruction(f, indent, displayer)?
            }
            TerminalInstr::Ite(instr) => {
                instr.display_instruction(f, indent, displayer)?
            }
            TerminalInstr::TailCall(instr) => write!(f, "{}", instr)?,
            TerminalInstr::TailCallIndirect(instr) => write!(f, "{}", instr)?,
            TerminalInstr::BranchTable(instr) => {
                instr.display_instruction(f, indent, displayer)?
            }
        }
        Ok(())
    }
}

/// Returns the returned value from to the function's caller.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ReturnInstr {
    return_values: SmallVec<[Value; 4]>,
}

impl fmt::Display for ReturnInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "return ")?;
        let requires_parens = self.return_values().len() >= 2;
        if requires_parens {
            write!(f, "(")?;
        }
        if let Some((first, rest)) = self.return_values().split_first() {
            write!(f, "{}", first)?;
            for return_value in rest {
                write!(f, ", {}", return_value)?;
            }
        }
        if requires_parens {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl ReturnInstr {
    /// Creates a new return instruction returning the given value.
    pub fn new<T>(return_values: T) -> Self
    where
        T: IntoIterator<Item = Value>,
    {
        Self {
            return_values: return_values.into_iter().collect::<SmallVec<_>>(),
        }
    }

    /// Returns the value that is returned by the instruction.
    #[inline]
    pub fn return_values(&self) -> &[Value] {
        &self.return_values
    }
}

impl VisitValues for ReturnInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for &value in &self.return_values {
            if !visitor(value) {
                break
            }
        }
    }
}

impl VisitValuesMut for ReturnInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        for value in &mut self.return_values {
            if !visitor(value) {
                break
            }
        }
    }
}

/// Unconditionally branches to another basic block.
#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[display(fmt = "br {}", edge)]
pub struct BranchInstr {
    edge: Edge,
}

impl BranchInstr {
    /// Creates a new unconditional branch instruction using the given branching edge.
    pub fn new(edge: Edge) -> Self {
        Self { edge }
    }

    /// Returns the branching edge of the unconditional branch.
    #[inline]
    pub fn edge(&self) -> Edge {
        self.edge
    }
}

impl DisplayInstruction for BranchInstr {
    fn display_instruction(
        &self,
        f: &mut fmt::Formatter,
        _indent: Indent,
        displayer: &dyn DisplayEdge,
    ) -> fmt::Result {
        write!(f, "branch ")?;
        displayer.display_edge(f, self.edge())?;
        Ok(())
    }
}

/// Conditionally either branches to `then` or `else` branch depending on `condition`.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct IfThenElseInstr {
    condition: Value,
    then_edge: Edge,
    else_edge: Edge,
}

impl IfThenElseInstr {
    /// Creates a new conditional branch instruction.
    ///
    /// Branches either to `then_edge` branching edge in case `condition` is
    /// non-zero (or `true`) or to `else_edge` branching edge otherwise.
    pub fn new(condition: Value, then_edge: Edge, else_edge: Edge) -> Self {
        Self {
            condition,
            then_edge,
            else_edge,
        }
    }

    /// Returns the condition value of the if-then-else instruction.
    #[inline]
    pub fn condition(&self) -> Value {
        self.condition
    }

    /// Returns the branching edge taken in case the condition evaluates to `true`.
    #[inline]
    pub fn then_edge(&self) -> Edge {
        self.then_edge
    }

    /// Returns the branching edge taken in case the condition evaluates to `false`.
    #[inline]
    pub fn else_edge(&self) -> Edge {
        self.else_edge
    }
}

impl VisitValues for IfThenElseInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.condition);
    }
}

impl VisitValuesMut for IfThenElseInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.condition);
    }
}

impl DisplayInstruction for IfThenElseInstr {
    fn display_instruction(
        &self,
        f: &mut fmt::Formatter,
        _indent: Indent,
        displayer: &dyn DisplayEdge,
    ) -> fmt::Result {
        write!(f, "if {} then ", self.condition())?;
        displayer.display_edge(f, self.then_edge())?;
        write!(f, " else ")?;
        displayer.display_edge(f, self.else_edge())?;
        Ok(())
    }
}

/// A tail call instruction.
#[derive(Debug, From, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TailCallInstr {
    /// The underlying call instruction.
    instr: CallInstr,
}

impl Display for TailCallInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "return {}", self.instr)
    }
}

impl TailCallInstr {
    /// Creates a new tail call instruction to call the indexed function using the given parameters.
    pub fn new<I>(func: Func, call_params: I) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            instr: CallInstr::new(func, call_params),
        }
    }

    /// Returns the called function index.
    pub fn func(&self) -> Func {
        self.instr.func()
    }

    /// Returns the function call parameters.
    pub fn params(&self) -> &[Value] {
        self.instr.params()
    }
}

impl VisitValues for TailCallInstr {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        self.instr.visit_values(visitor)
    }
}

impl VisitValuesMut for TailCallInstr {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        self.instr.visit_values_mut(visitor)
    }
}

/// A indirect tail call instruction.
#[derive(Debug, From, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TailCallIndirectInstr {
    /// The underlying indirect call instruction.
    instr: CallIndirectInstr,
}

impl Display for TailCallIndirectInstr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "return {}", self.instr)
    }
}

impl TailCallIndirectInstr {
    /// Creates a new call instruction to call the indexed function using the given parameters.
    pub fn new<I>(
        table: Table,
        func_type: FuncType,
        index: Value,
        call_params: I,
    ) -> Self
    where
        I: IntoIterator<Item = Value>,
    {
        Self {
            instr: CallIndirectInstr::new(table, func_type, index, call_params),
        }
    }

    /// Returns the table for the indirect function call.
    pub fn table(&self) -> Table {
        self.instr.table()
    }

    /// Returns the table index for the indirect call.
    pub fn index(&self) -> Value {
        self.instr.index()
    }

    /// Returns the expected function type of the indirectly called function.
    pub fn func_type(&self) -> FuncType {
        self.instr.func_type()
    }

    /// Returns the SSA function input values for the indirect call.
    pub fn params(&self) -> &[Value] {
        self.instr.params()
    }
}

impl VisitValues for TailCallIndirectInstr {
    fn visit_values<V>(&self, visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        self.instr.visit_values(visitor)
    }
}

impl VisitValuesMut for TailCallIndirectInstr {
    fn visit_values_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        self.instr.visit_values_mut(visitor)
    }
}

/// A branching table mapping indices to branching targets.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct BranchTableInstr {
    selector: Value,
    default_edge: Edge,
    target_edges: SmallVec<[Edge; 4]>,
}

impl BranchTableInstr {
    /// Creates a new branching table with the given case, default target and targets.
    pub fn new<T>(selector: Value, default_edge: Edge, target_edges: T) -> Self
    where
        T: IntoIterator<Item = Edge>,
    {
        Self {
            selector,
            default_edge,
            target_edges: target_edges.into_iter().collect(),
        }
    }

    /// Returns the selector value determining where to jump to.
    pub fn selector(&self) -> Value {
        self.selector
    }

    /// Returns a slice over all target jumps.
    pub fn target_edges(&self) -> &[Edge] {
        &self.target_edges
    }

    /// Returns the default target to jump to.
    pub fn default_target(&self) -> Edge {
        self.default_edge
    }
}

impl VisitValues for BranchTableInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        visitor(self.selector);
    }
}

impl VisitValuesMut for BranchTableInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        visitor(&mut self.selector);
    }
}

impl DisplayInstruction for BranchTableInstr {
    fn display_instruction(
        &self,
        f: &mut fmt::Formatter,
        indent: Indent,
        displayer: &dyn DisplayEdge,
    ) -> fmt::Result {
        let target_indentation = indent + Indent::single();
        writeln!(f, "match {} {{", self.selector())?;
        if let Some((first, rest)) = self.target_edges().split_first() {
            write!(f, "{}0 🠖 ", target_indentation)?;
            displayer.display_edge(f, *first)?;
            for (n, edge) in rest.iter().enumerate() {
                writeln!(f, ",")?;
                write!(f, "{}{} 🠖 ", target_indentation, n + 1)?;
                displayer.display_edge(f, *edge)?;
            }
            writeln!(f, ",")?;
        }
        writeln!(f, "{}_ 🠖 {}", target_indentation, self.default_target())?;
        write!(f, "{}}}", indent)?;
        Ok(())
    }
}

macro_rules! impl_from_terminal_instr_for_instr {
    ( $( $name:ident ),* $(,)? ) => {
        $(
            impl ::core::convert::From<$name> for crate::instr::Instruction {
                fn from(instr: $name) -> Self {
                    Self::Terminal(crate::instr::TerminalInstr::from(instr))
                }
            }
        )*
    };
}
impl_from_terminal_instr_for_instr! {
    ReturnInstr,
    BranchInstr,
    IfThenElseInstr,
    BranchTableInstr,
    TailCallInstr,
    TailCallIndirectInstr,
}
