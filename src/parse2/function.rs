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

use super::{FunctionId, ParseError, Type};
use core::convert::TryFrom;
use std::iter::FusedIterator;
use wasmparser::{
    BinaryReader,
    FuncValidator,
    LocalsReader,
    Operator,
    OperatorsReader,
    ValidatorResources,
};

/// A parsed and validated function body in the Wasm input binary.
///
/// Allows for simple and efficient access to locals and operators.
pub struct FunctionBody<'a> {
    id: FunctionId,
    body: wasmparser::FunctionBody<'a>,
    count_operators: u32,
}

impl<'a> FunctionBody<'a> {
    /// Creates a new function body if it parses and validates correctly.
    pub fn new(
        id: FunctionId,
        validator: &mut FuncValidator<ValidatorResources>,
        body: wasmparser::FunctionBody<'a>,
    ) -> Result<Self, ParseError> {
        let mut reader = body.get_binary_reader();
        Self::validate_locals(validator, &mut reader)?;
        let count_operators = Self::validate_operators(validator, &mut reader)?;
        let offset = reader.original_position();
        validator.finish(offset)?;
        Ok(Self {
            id,
            body,
            count_operators,
        })
    }

    /// Parses and validates the locals of the input function body and checks if their types are supported.
    fn validate_locals(
        validator: &mut FuncValidator<ValidatorResources>,
        reader: &mut BinaryReader,
    ) -> Result<(), ParseError> {
        let count_locals = reader.read_var_u32()?;
        for _ in 0..count_locals {
            let offset = reader.original_position();
            let count = reader.read_var_u32()?;
            let ty = reader.read_type()?;
            validator.define_locals(offset, count, ty)?;
            Type::try_from(ty)?;
        }
        Ok(())
    }

    /// Parses and validates the operators of the input function body.
    ///
    /// Returns the number of operators in the function body.
    fn validate_operators(
        validator: &mut FuncValidator<ValidatorResources>,
        reader: &mut BinaryReader,
    ) -> Result<u32, ParseError> {
        let mut count_operators = 0;
        while !reader.eof() {
            let offset = reader.original_position();
            let op = reader.read_operator()?;
            validator.op(offset, &op)?;
            count_operators += 1;
        }
        Ok(count_operators)
    }

    /// Returns the unique ID of the function.
    pub fn id(&self) -> FunctionId {
        self.id
    }

    /// Returns an iterator over all local variable entries of the function body.
    pub fn locals(&self) -> LocalsIter<'a> {
        let locals_reader = self
            .body
            .get_locals_reader()
            .expect("expected since enforced at the new constructor");
        let locals_count = locals_reader.get_count();
        LocalsIter {
            reader: locals_reader,
            remaining: locals_count,
        }
    }

    /// Returns an iterator over all operators of the function body.
    pub fn ops(&self) -> OperatorsIter<'a> {
        let ops_reader = self
            .body
            .get_operators_reader()
            .expect("expected since enforced at the new constructor");
        let ops_count = self.count_operators;
        OperatorsIter {
            reader: ops_reader,
            remaining: ops_count,
        }
    }
}

/// The original position of the yielded entity in the input Wasm binary.
///
/// Useful for more precise error reporting.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct OriginalPosition(usize);

impl OriginalPosition {
    /// Returns the original position as `usize` value.
    pub fn get(self) -> usize {
        self.0
    }
}

/// Iterator over the local variable entries of a function body.
pub struct LocalsIter<'a> {
    reader: LocalsReader<'a>,
    remaining: u32,
}

/// A local variable entry consisting of the amount and type of the local variables.
#[derive(Debug)]
pub struct LocalVariableEntry {
    count: u32,
    ty: Type,
}

impl LocalVariableEntry {
    /// Returns the number of local variables in this entry.
    pub fn count(&self) -> u32 {
        self.count
    }

    /// Returns the type of the local variables in this entry.
    pub fn ty(&self) -> Type {
        self.ty
    }
}

impl<'a> Iterator for LocalsIter<'a> {
    type Item = (OriginalPosition, LocalVariableEntry);

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.remaining as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        let position = self.reader.original_position();
        let (count, ty) = self
            .reader
            .read()
            .expect("expected since enforced at the new constructor");
        let ty = Type::try_from(ty)
            .expect("expected since enforced at the new constructor");
        Some((OriginalPosition(position), LocalVariableEntry { count, ty }))
    }
}

impl<'a> ExactSizeIterator for LocalsIter<'a> {}
impl<'a> FusedIterator for LocalsIter<'a> {}

/// Iterator over the operators of a function body.
pub struct OperatorsIter<'a> {
    reader: OperatorsReader<'a>,
    remaining: u32,
}

impl<'a> Iterator for OperatorsIter<'a> {
    type Item = (OriginalPosition, Operator<'a>);

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.remaining as usize;
        (remaining, Some(remaining))
    }

    fn next(&mut self) -> Option<Self::Item> {
        let position = self.reader.original_position();
        let operator = self
            .reader
            .read()
            .expect("expected since enforced at the new constructor");
        Some((OriginalPosition(position), operator))
    }
}

impl<'a> ExactSizeIterator for OperatorsIter<'a> {}
impl<'a> FusedIterator for OperatorsIter<'a> {}
