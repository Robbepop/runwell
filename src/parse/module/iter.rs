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

use crate::parse::{
    Function,
    FunctionBody,
    FunctionId,
    FunctionSigId,
    Module,
};

/// Iterator over the internal functions of a Wasm module.
pub struct InternalFnIter<'a> {
    /// The underlying Wasm module.
    module: &'a Module,
    /// The slice over function signatures.
    fn_sigs: &'a [FunctionSigId],
    /// The slice over function bodies.
    fn_bodies: &'a [FunctionBody],
    /// Current start.
    start: usize,
    /// Current end.
    end: usize,
}

impl<'a> InternalFnIter<'a> {
    /// Creates a new internal function iterator for the given Wasm module.
    pub(super) fn new(module: &'a Module) -> Self {
        let fn_sigs = module.fn_sigs.internal_entities_slice();
        let fn_bodies = &module.fn_bodies[..];
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

    /// Queries the yielded pair for the given internal index.
    fn query_for(
        &self,
        internal_id: usize,
    ) -> (Function<'a>, &'a FunctionBody) {
        let fn_id = FunctionId::from_u32(
            // We are given an internal index and have to convert that
            // into a normal index before we use it to index into the
            // function signatures.
            internal_id as u32
                + self.module.fn_sigs.len_imported() as u32,
        );
        let fn_sig = self.module.types.get(self.fn_sigs[internal_id]);
        let function = Function::new(fn_id, fn_sig);
        let fn_body = &self.module.fn_bodies[internal_id];
        (function, fn_body)
    }
}

impl<'a> Iterator for InternalFnIter<'a> {
    type Item = (Function<'a>, &'a FunctionBody);

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let start = self.start;
        let res = self.query_for(start);
        self.start += 1;
        Some(res)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.start;
        (remaining, Some(remaining))
    }
}

impl<'a> core::iter::DoubleEndedIterator for InternalFnIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None
        }
        let end = self.end;
        let res = self.query_for(end);
        self.end -= 1;
        Some(res)
    }
}

impl<'a> core::iter::ExactSizeIterator for InternalFnIter<'a> {}

impl<'a> core::iter::FusedIterator for InternalFnIter<'a> {}
