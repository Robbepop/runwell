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
    /// Contains the selector integer type followed by all result types.
    ///
    /// By definition always stores at least two values.
    selector_and_result_types: SmallVec<[Type; 8]>,
    /// Represents the `selector` value followed by all match arm
    /// result values and finally including the default result values.
    ///
    /// By definition always stores at least two values.
    selector_and_result_values: SmallVec<[Value; 4]>,
}

/// Builder used to incrementally build up a multi-value returning match select instruction.
#[derive(Debug)]
pub struct MatchSelectInstrBuilder {
    /// The instruction under construction.
    instr: MatchSelectInstr,
    /// The number of already processed match arms.
    len_arms: u64,
}

impl MatchSelectInstrBuilder {
    /// Pushes another results tuple match arm to the constructed `MatchSelectInstr`.
    ///
    /// # Panics
    ///
    /// If the `results` tuple iterator does not yield exactly as many values as there
    /// are expected return types for the constructed `MatchSelectInstr`.
    pub fn push_results<T>(&mut self, results: T)
    where
        T: IntoIterator<Item = Value>,
    {
        let selector_type = self.instr.selector_type();
        let max_selector = selector_type.max_unsigned_value();
        if self.len_arms == max_selector {
            panic!(
                "cannot have more than {} match arms with a selector type of {}",
                max_selector,
                selector_type,
            )
        }
        self.instr.push_results(results);
        self.len_arms += 1;
    }

    /// Pushes the default results tuple to the constructed `MatchSelectInstr`.
    ///
    /// # Panics
    ///
    /// If the `results` tuple iterator does not yield exactly as many values as there
    /// are expected return types for the constructed `MatchSelectInstr`.
    pub fn finish<T>(mut self, default_results: T) -> MatchSelectInstr
    where
        T: IntoIterator<Item = Value>,
    {
        self.instr.push_results(default_results);
        self.instr
    }
}

impl MatchSelectInstr {
    /// Pushes another result tuple match arm to the multi-match select instruction.
    ///
    /// # Note
    ///
    /// This is a private API meant to be used primarily by the `MatchSelectInstrBuilder`.
    ///
    /// # Panics
    ///
    /// If the `results` tuple iterator does not yield exactly as many values as there
    /// are expected return types for the constructed `MatchSelectInstr`.
    fn push_results<T>(&mut self, results: T)
    where
        T: IntoIterator<Item = Value>,
    {
        let len_before = self.selector_and_result_values.len();
        self.selector_and_result_values.extend(results);
        let len_after = self.selector_and_result_values.len();
        assert_eq!(len_after - len_before, self.result_types().len())
    }

    /// Creates a new select operation returning one value tuple out of a set of value tuples.
    ///
    /// # Panics
    ///
    /// If the `result_types` iterator yields zero types.
    pub fn new_multi<T>(
        selector: Value,
        selector_type: IntType,
        result_types: T,
    ) -> MatchSelectInstrBuilder
    where
        T: IntoIterator<Item = Type>,
    {
        let mut selector_and_result_types = smallvec![selector_type.into()];
        selector_and_result_types.extend(result_types);
        assert!(
            selector_and_result_types.len() > 1,
            "encountered 0 result types for the match select instruction but require at least 1",
        );
        MatchSelectInstrBuilder {
            instr: Self {
                selector_and_result_types,
                selector_and_result_values: smallvec![selector],
            },
            len_arms: 0,
        }
    }

    /// Creates a new select operation returning a single value out of a set of values.
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
        let mut selector_and_result_types = smallvec![selector_type.into()];
        selector_and_result_types.extend([result_type].iter().copied());
        let mut selector_and_result_values = smallvec![selector];
        selector_and_result_values.extend(target_results);
        selector_and_result_values.push(default_result);
        Self {
            selector_and_result_types,
            selector_and_result_values,
        }
    }

    /// Returns the type of the selector.
    pub fn selector_type(&self) -> IntType {
        match self.selector_and_result_types[0] {
            Type::Int(int_type) => int_type,
            _ => unreachable!(
                "by construction cannot contain a non-integer type in the first position"
            ),
        }
    }

    /// Returns the shared type of all result values.
    pub fn result_types(&self) -> &[Type] {
        &self.selector_and_result_types[1..]
    }

    /// Returns the value of the selector.
    pub fn selector(&self) -> Value {
        self.selector_and_result_values[0]
    }

    /// Returns the value of the default result.
    ///
    /// This is taken if no other target result matches
    /// the selector.
    pub fn default_results(&self) -> &[Value] {
        let len_values = self.selector_and_result_values.len();
        let len_results = self.result_types().len();
        &self.selector_and_result_values[(len_values - len_results)..]
    }

    /// Returns a slice over the target results associated to the given index if any.
    pub fn target_results(&self, at: usize) -> Option<&[Value]> {
        let len_values = self.selector_and_result_values.len();
        let len_results = self.result_types().len();
        let target_results =
            &self.selector_and_result_values[1..(len_values - len_results)];
        let offset = at * len_results;
        target_results.get(offset..(offset + len_results))
    }
}

impl VisitValues for MatchSelectInstr {
    fn visit_values<V>(&self, mut visitor: V)
    where
        V: FnMut(Value) -> bool,
    {
        for value in self.selector_and_result_values.iter().copied() {
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
        for value in self.selector_and_result_values.iter_mut() {
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
        write!(f, "match<{}, ", self.selector_type())?;
        if let Some((first, rest)) = self.result_types().split_first() {
            if rest.is_empty() {
                write!(f, "{}", first)?;
            } else {
                write!(f, "({}", first)?;
                for ty in rest {
                    write!(f, ", {}", ty)?;
                }
                write!(f, ")")?;
            }
        }
        writeln!(f, "> {{")?;
        let mut current = 0;
        while let Some(results) = self.target_results(current) {
            match self.selector_type() {
                IntType::I1 => write!(f, "{}false", target_indentation)?,
                _ => write!(f, "{}{}", target_indentation, current)?,
            };
            write!(f, " => ")?;
            if let Some((first, rest)) = results.split_first() {
                if rest.is_empty() {
                    write!(f, "{}", first)?;
                } else {
                    write!(f, "({}", first)?;
                    for result in rest {
                        write!(f, ", {}", result)?;
                    }
                    write!(f, ")")?;
                }
            }
            writeln!(f, ",")?;
            current += 1;
        }
        match self.selector_type() {
            IntType::I1 => write!(f, "{}true ", target_indentation)?,
            _ => write!(f, "{}_", target_indentation)?,
        };
        write!(f, " => ")?;
        if let Some((first, rest)) = self.default_results().split_first() {
            if rest.is_empty() {
                write!(f, "{}", first)?;
            } else {
                write!(f, "({}", first)?;
                for result in rest {
                    write!(f, ", {}", result)?;
                }
                write!(f, ")")?;
            }
        }
        writeln!(f, ",")?;
        write!(f, "{}}}", indent)?;
        Ok(())
    }
}
