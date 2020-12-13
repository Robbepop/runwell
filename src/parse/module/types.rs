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

use crate::parse::{FunctionSigId, ComilerError, Type};
use core::convert::TryFrom;
use derive_more::Display;

#[derive(Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypesError {
    #[display(
        fmt = "encountered duplicate reservation for types table with {}. previous reservation: {}",
        total_count,
        previous
    )]
    DuplicateReserved { total_count: u32, previous: u32 },
    #[display(
        fmt = "tried to register another type when the Wasm types table did not expect any further items. reserved: {}, last item = {:?}",
        reserved,
        last_item
    )]
    RegisteredTooManyTypes {
        reserved: u32,
        last_item: FunctionSig,
    },
}

/// A function signature.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionSig {
    /// The amount of inputs.
    len_inputs: usize,
    /// All input types followed by all output types.
    ///
    /// The `len_inputs` field denotes the cut.
    inputs_outputs: Box<[Type]>,
}

impl TryFrom<wasmparser::FuncType> for FunctionSig {
    type Error = ComilerError;

    fn try_from(func_ty: wasmparser::FuncType) -> Result<Self, Self::Error> {
        let inputs = func_ty
            .params
            .iter()
            .cloned()
            .map(Type::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = func_ty
            .returns
            .iter()
            .cloned()
            .map(Type::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self::new(inputs, outputs))
    }
}

impl FunctionSig {
    /// Creates a new function signature.
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

/// The Wasm types table.
///
/// Represents the contents of the Wasm type section.
#[derive(Debug, Default)]
pub struct Types {
    types: Vec<FunctionSig>,
}

impl Types {
    /// Reserves space for the given amount of expected type definitions.
    ///
    /// # Errors
    ///
    /// If there already has been a reservation before.
    pub fn reserve(&mut self, total_count: u32) -> Result<(), ComilerError> {
        let capacity = self.types.capacity();
        if capacity > 0 {
            return Err(TypesError::DuplicateReserved {
                total_count,
                previous: capacity as u32,
            })
            .map_err(Into::into)
        }
        self.types.reserve(total_count as usize);
        Ok(())
    }

    /// Returns the number of registered Wasm type definitions.
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// Returns the function signature identified by `id`.
    ///
    /// # Panics
    ///
    /// If the given ID is invalid for this Wasm types table.
    pub fn get(&self, id: FunctionSigId) -> &FunctionSig {
        &self.types[id.into_u32() as usize]
    }

    /// Returns the function signature identifier by `id` if any.
    pub fn try_get(&self, id: FunctionSigId) -> Option<&FunctionSig> {
        self.types.get(id.into_u32() as usize)
    }

    /// Registers another function signature at the Wasm types table.
    ///
    /// Returns its unique function signature ID.
    ///
    /// # Errors
    ///
    /// If trying to register more types than reserved.
    pub fn push(
        &mut self,
        sig: FunctionSig,
    ) -> Result<FunctionSigId, TypesError> {
        let len = self.len();
        let cap = self.types.capacity();
        assert!(len < u32::MAX as usize);
        if len == cap {
            return Err(TypesError::RegisteredTooManyTypes {
                reserved: cap as u32,
                last_item: sig,
            })
            .map_err(Into::into)
        }
        let id = FunctionSigId::from_u32(self.len() as u32);
        self.types.push(sig);
        Ok(id)
    }
}
