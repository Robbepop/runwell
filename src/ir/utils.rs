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

use crate::parse::Identifier;
use core::num::NonZeroUsize;

/// A block identifier within a function that allows to jump to.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BlockId(NonZeroUsize);

impl Identifier for BlockId {
    /// Returns the underlying `usize` value.
    fn get(self) -> usize {
        self.0.get()
    }
}

/// An SSA instruction binding.
#[derive(Debug, Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct Binding(NonZeroUsize);

impl Identifier for Binding {
    /// Returns the underlying `usize` value.
    fn get(self) -> usize {
        self.0.get()
    }
}

/// Generates new unique binding.
#[derive(Debug)]
pub struct BindingGen {
    /// The current value identifier.
    current: usize,
}

impl BindingGen {
    /// Creates a new binding generator.
    pub fn new() -> Self {
        Self {
            // We start at `1` because bindings are non-zero.
            current: 1,
        }
    }

    /// Resets the binding generator.
    pub fn reset(&mut self) {
        self.current = 1;
    }

    /// Generates a new unique binding identifier.
    pub fn gen(&mut self) -> Binding {
        let result = Binding(
            NonZeroUsize::new(self.current).expect("we start counting at 1"),
        );
        self.current += 1;
        result
    }
}
