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

use super::DefinedEntityIter;
use crate::parse::{Function, FunctionBody, FunctionId, FunctionSigId, Module};
use core::{iter::DoubleEndedIterator, slice::Iter as SliceIter};

type FnSigsIter<'a> = DefinedEntityIter<'a, FunctionId, FunctionSigId, ()>;

/// Iterator over the internal functions of a Wasm module.
pub struct InternalFnIter<'a> {
    /// The underlying Wasm module.
    module: &'a Module,
    /// The slice over function signatures.
    fn_sigs: FnSigsIter<'a>,
    /// The slice over function bodies.
    fn_bodies: SliceIter<'a, FunctionBody>,
    /// Index incremented with `next`.
    start: usize,
    /// Index decremented with `next_back`.
    end: usize,
}

impl<'a> InternalFnIter<'a> {
    /// Creates a new internal function iterator for the given Wasm module.
    pub(super) fn new(module: &'a Module) -> Self {
        let fn_sigs = module
            .fn_sigs
            .iter_defined()
            .expect("encountered unexpected invalid function signature table");
        let fn_bodies = module.fn_bodies.iter();
        // We should assume that both of these slices are the same
        // but to be extra defensive we want to also assert it.
        assert_eq!(fn_sigs.len(), fn_bodies.len());
        let end = fn_sigs.len();
        Self {
            module,
            fn_sigs,
            fn_bodies,
            start: 0,
            end,
        }
    }

    /// Returns the current function ID.
    fn current_id(&self, raw_index: usize) -> FunctionId {
        FunctionId::from_u32(
            // We are given an internal index and have to convert that
            // into a normal index before we use it to index into the
            // function signatures.
            raw_index as u32 + self.module.fn_sigs.len_imported() as u32,
        )
    }
}

impl<'a> Iterator for InternalFnIter<'a> {
    type Item = (Function<'a>, &'a FunctionBody);

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let start = self.start;
        let id = self.current_id(start);
        let fn_sig_id = self.fn_sigs.next()?.decl;
        let fn_body = self.fn_bodies.next()?;
        let fn_sig = self.module.types.get(*fn_sig_id);
        self.start += 1;
        Some((Function::new(id, fn_sig), fn_body))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.start;
        (remaining, Some(remaining))
    }
}

impl<'a> DoubleEndedIterator for InternalFnIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        self.end -= 1;
        let id = self.current_id(self.end);
        let fn_sig_id = self.fn_sigs.next_back()?.decl;
        let fn_body = self.fn_bodies.next_back()?;
        let fn_sig = self.module.types.get(*fn_sig_id);
        Some((Function::new(id, fn_sig), fn_body))
    }
}

impl<'a> core::iter::ExactSizeIterator for InternalFnIter<'a> {}

impl<'a> core::iter::FusedIterator for InternalFnIter<'a> {}
