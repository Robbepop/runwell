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

use crate::parse::FunctionId;
use derive_more::From;
use wasmparser::{Operator, Type};

/// A function signature.
#[derive(Debug, From)]
pub struct FunctionSig {
    /// The underlying function type.
    fn_type: wasmparser::FuncType,
}

impl FunctionSig {
    /// Returns a slice over the input types of `self`.
    pub fn inputs(&self) -> &[Type] {
        &self.fn_type.params
    }

    /// Returns a slice over the output types of `self`.
    pub fn outputs(&self) -> &[Type] {
        &self.fn_type.returns
    }
}

/// A function.
#[derive(Debug)]
pub struct Function<'a> {
    /// The function index.
    id: FunctionId,
    /// The function signature.
    sig: &'a FunctionSig,
}

impl<'a> Function<'a> {
    /// Creates a new function from the given ID and signature.
    pub(crate) fn new(id: FunctionId, sig: &'a FunctionSig) -> Self {
        Self { id, sig }
    }

    /// Returns the function ID.
    pub fn id(&self) -> FunctionId {
        self.id
    }

    /// Returns the function signature.
    pub fn sig(&self) -> &FunctionSig {
        self.sig
    }
}

/// A function body.
#[derive(Debug, From)]
pub struct FunctionBody<'a> {
    /// The locals of the function.
    locals: Vec<(usize, Type)>,
    /// The operations of the function.
    ops: Vec<Operator<'a>>,
}

impl<'a> FunctionBody<'a> {
    /// Creates a new function body.
    pub(crate) fn new<L, O>(locals: L, ops: O) -> Self
    where
        L: IntoIterator<Item = (usize, Type)>,
        O: IntoIterator<Item = Operator<'a>>,
    {
        let locals = locals.into_iter().collect::<Vec<_>>();
        let ops = ops.into_iter().collect::<Vec<_>>();
        Self { locals, ops }
    }

    /// Returns the local variable declarations of the function body.
    pub fn locals(&self) -> &[(usize, Type)] {
        &self.locals
    }

    /// Returns the operations of the function body.
    pub fn ops(&self) -> &[Operator<'a>] {
        &self.ops
    }
}
