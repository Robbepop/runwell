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

use core::fmt;

use crate::{
    primitive::{IntType, Type, Value},
    DisplayEdge,
    DisplayInstruction,
    Indent,
    VisitValues,
    VisitValuesMut,
};
use smallvec::{smallvec, SmallVec};

/// Selects a value from a table of values without IR-level branching.
///
/// # Note
///
/// This might result in conditional branches when translating to
/// machine code on some architectures.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct MatchSelectInstr {
    /// The type of the selector.
    selector_type: IntType,
    /// The shared type of all result values.
    result_type: Type,
    /// Represents the `selector` value, followed by the default
    /// result and all target results.
    ///
    /// By definition always stores at least two values.
    selector_and_results: SmallVec<[Value; 4]>,
}

impl MatchSelectInstr {
    /// Creates a new select operation.
    pub fn new<T>(
        selector: Value,
        selector_type: IntType,
        result_type: Type,
        default_result: Value,
        target_results: T,
    ) -> Self
    where
        T: IntoIterator<Item = Value>,
    {
        let mut selector_and_results = smallvec![selector, default_result];
        selector_and_results.extend(target_results);
        Self {
            selector_type,
            result_type,
            selector_and_results,
        }
    }

    /// Returns the type of the selector.
    pub fn selector_type(&self) -> IntType {
        self.selector_type
    }

    /// Returns the shared type of all result values.
    pub fn result_type(&self) -> Type {
        self.result_type
    }

    /// Returns the value of the selector.
    pub fn selector(&self) -> Value {
        self.selector_and_results[0]
    }

    /// Returns the value of the default result.
    ///
    /// This is taken if no other target result matches
    /// the selector.
    pub fn default_result(&self) -> Value {
        self.selector_and_results[1]
    }

    /// Returns a slice over all target results.
    pub fn target_results(&self) -> &[Value] {
        &self.selector_and_results[2..]
    }
}

impl VisitValues for MatchSelectInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for value in self.selector_and_results.iter().copied() {
            if !visitor(value) {
                break
            }
        }
    }
}

impl VisitValuesMut for MatchSelectInstr {
    fn visit_values_mut<V>(&mut self, mut visitor: V)
    where
        V: FnMut(&mut Value) -> bool,
    {
        for value in self.selector_and_results.iter_mut() {
            if !visitor(value) {
                break
            }
        }
    }
}

impl DisplayInstruction for MatchSelectInstr {
    fn display_instruction(
        &self,
        f: &mut fmt::Formatter,
        indent: Indent,
        _displayer: &dyn DisplayEdge,
    ) -> fmt::Result {
        let target_indentation = indent + Indent::single();
        writeln!(
            f,
            "match<{}, {}> {} {{",
            self.selector_type(),
            self.result_type(),
            self.selector()
        )?;
        if let Some((first, rest)) = self.target_results().split_first() {
            let first_matcher = match self.selector_type() {
                IntType::I1 => "false",
                _ => "0",
            };
            write!(f, "{}{} 🠖 {}", target_indentation, first_matcher, first)?;
            for (n, result) in rest.iter().enumerate() {
                writeln!(f, ",")?;
                write!(f, "{}{} 🠖 {}", target_indentation, n + 1, result)?;
            }
            writeln!(f, ",")?;
        }
        let default_matcher = match self.selector_type() {
            IntType::I1 => "true ",
            _ => "_",
        };
        writeln!(
            f,
            "{}{} 🠖 {}",
            target_indentation,
            default_matcher,
            self.default_result()
        )?;
        write!(f, "{}}}", indent)?;
        Ok(())
    }
}
