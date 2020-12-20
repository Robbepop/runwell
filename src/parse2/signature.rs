// Copyright 2020 Robin Freyler
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

use super::{ParseError, Type};
use core::convert::TryFrom;

/// A function type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionType {
    /// The amount of inputs.
    len_inputs: usize,
    /// All input types followed by all output types.
    ///
    /// The `len_inputs` field denotes the cut.
    inputs_outputs: Box<[Type]>,
}

impl TryFrom<wasmparser::FuncType> for FunctionType {
    type Error = ParseError;

    fn try_from(func_ty: wasmparser::FuncType) -> Result<Self, Self::Error> {
        let inputs = func_ty
            .params
            .iter()
            .copied()
            .map(Type::try_from)
            .collect::<Result<Vec<_>, _>>()
            .map_err(ParseError::from)
            .map_err(|err| {
                err.with_context("invalid or unsupported type for function input")
            })?;
        let outputs = func_ty
            .returns
            .iter()
            .copied()
            .map(Type::try_from)
            .collect::<Result<Vec<_>, _>>()
            .map_err(ParseError::from)
            .map_err(|err| {
                err.with_context("invalid or unsupported type for function output")
            })?;
        Ok(Self::new(inputs, outputs))
    }
}

impl FunctionType {
    /// Creates a new function type.
    pub fn new<I, O>(inputs: I, outputs: O) -> Self
    where
        I: IntoIterator<Item = Type>,
        O: IntoIterator<Item = Type>,
    {
        let mut inputs_outputs = Vec::new();
        inputs_outputs.extend(inputs.into_iter());
        let len_inputs = inputs_outputs.len();
        inputs_outputs.extend(outputs.into_iter());
        Self {
            len_inputs,
            inputs_outputs: inputs_outputs.into_boxed_slice(),
        }
    }

    /// Returns a slice over the input types of `self`.
    pub fn inputs(&self) -> &[Type] {
        &self.inputs_outputs[..self.len_inputs]
    }

    /// Returns a slice over the output types of `self`.
    pub fn outputs(&self) -> &[Type] {
        &self.inputs_outputs[self.len_inputs..]
    }
}
