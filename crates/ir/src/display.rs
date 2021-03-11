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

use crate::primitive::Edge;
use core::fmt;

/// Implemented by all Runwell IR instructions to display within context.
pub trait DisplayInstruction {
    fn display_instruction(
        &self,
        f: &mut dyn fmt::Write,
        indent: Indent,
        displayer: &dyn DisplayEdge,
    ) -> fmt::Result;
}

/// Allows to customize display of branching edges in the Runwell IR.
///
/// Some Runwell IR instructions make use of `DisplayEdge` implementers
/// in order to properly display branching edges.
///
/// # Note
///
/// Runwell IR instruction use the `Edge` type to signal branches.
/// However, the `Edge` is just a shallow type that by itself does
/// not carry any associated information. Instead enclosing types
/// of Runwell IR instructions are meant to carry information
/// associated to edges. Those implement `DisplayEdge` and Runwell
/// IR instructions then can use this trait in order to properly
/// display branching edges.
pub trait DisplayEdge {
    /// Displays the given branching edge using the formatter.
    fn display_edge(&self, f: &mut dyn fmt::Write, edge: Edge) -> fmt::Result;
}

/// A single indentation.
///
/// Used for printing modules, functions, function bodies at different indentation levels.
#[derive(Debug, Default, Copy, Clone)]
pub struct Indent(usize);

impl Indent {
    /// Creates a single indentation.
    pub fn single() -> Self {
        Self(1)
    }
}

impl core::ops::Add<Self> for Indent {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl fmt::Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        core::iter::repeat(" ")
            .take(self.0 * 4)
            .try_for_each(|ws| write!(f, "{}", ws))
    }
}
