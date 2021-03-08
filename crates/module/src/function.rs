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

use crate::{primitive::FunctionType, FunctionBody};
use core::fmt;
use entity::RawIdx;
use ir::{
    primitive::{Func, Type, Value},
    Indent,
};

/// A Runwell function.
///
/// Includes the function's unique index, signature and body.
///
/// This is a short-lived composite type used as merge point for
/// all information regarding a single Runwell function.
#[derive(Debug, Copy, Clone)]
pub struct Function<'a> {
    func: Func,
    func_type: &'a FunctionType,
    func_body: &'a FunctionBody,
}

impl<'a> Function<'a> {
    /// Creates a new function.
    pub(super) fn new(
        func: Func,
        func_type: &'a FunctionType,
        func_body: &'a FunctionBody,
    ) -> Self {
        Self {
            func,
            func_type,
            func_body,
        }
    }

    /// Returns the function's unique index.
    #[inline]
    pub fn idx(&self) -> Func {
        self.func
    }

    /// Returns the function's signature.
    #[inline]
    pub fn ty(&self) -> &'a FunctionType {
        &self.func_type
    }

    /// Returns the function's input types.
    #[inline]
    pub fn inputs(&self) -> &'a [Type] {
        self.func_type.inputs()
    }

    /// Returns the function's output types.
    #[inline]
    pub fn outputs(&self) -> &'a [Type] {
        self.func_type.outputs()
    }

    /// Returns the function body.
    #[inline]
    pub fn body(&self) -> &'a FunctionBody {
        &self.func_body
    }

    /// Displays the function using the given indentation.
    pub(crate) fn display_with_indent(
        &self,
        f: &mut fmt::Formatter,
        indent: Indent,
    ) -> Result<(), fmt::Error> {
        let inputs = self
            .inputs()
            .iter()
            .enumerate()
            .map(|(n, ty)| {
                let val = Value::from_raw(RawIdx::from_u32(n as u32));
                (val, ty)
            })
            .collect::<Vec<_>>();
        write!(f, "{}fn {}(", indent, self.idx())?;
        if let Some(((first_value, first_type), rest)) = inputs.split_first() {
            write!(f, "{}: {}", first_value, first_type)?;
            for (rest_value, rest_type) in rest {
                write!(f, ", {}: {}", rest_value, rest_type)?;
            }
        }
        write!(f, ")")?;
        if let Some((first_output, rest)) = self.outputs().split_first() {
            write!(f, " -> ")?;
            let just_one_output = self.outputs().len() == 1;
            if !just_one_output {
                write!(f, "(")?;
            }
            write!(f, "{}", first_output)?;
            for rest_output in rest {
                write!(f, ", {}", rest_output)?;
            }
            if !just_one_output {
                write!(f, ")")?;
            }
        }
        writeln!(f, " {{")?;
        self.body()
            .display_with_indent(f, indent + Indent::single())?;
        writeln!(f, "{}}}", indent)?;
        Ok(())
    }
}

impl<'a> fmt::Display for Function<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_with_indent(f, Default::default())
    }
}
