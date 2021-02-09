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

use derive_more::{Display, Error};

/// An error that occured while translating from Wasm to Runwell IR.
#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum TranslateError {
    #[display(fmt = "encountered unsupported Wasm operator at {}", offset)]
    UnsupportedOperator { offset: usize },
    #[display(
        fmt = "encountered supported but unimplemented Wasm operator: {}",
        display
    )]
    UnimplementedOperator { display: String },
    #[display(
        fmt = "missing value in emulation stack. found {} but expected {}.",
        found,
        expected
    )]
    MissingStackValue { expected: u32, found: u32 },
    #[display(
        fmt = "expected Wasm `Block` or `Loop` due to validation but block stack was empty"
    )]
    MissingWasmBlock,
    #[display(
        fmt = "tried to access the {}-th Wasm block from the block stack with a length of just {}",
        n,
        len
    )]
    RelativeDepthExceedsBlockStack {
        /// The n-th index (from back) that was tried to accessed.
        n: u32,
        /// The current length of the block stack.
        len: usize,
    },
}

impl TranslateError {
    /// Creates a new error indicating that a supported but unimplemented
    /// Wasm operator has been encountered.
    pub fn unimplemented_operator(op: wasmparser::Operator) -> Self {
        Self::UnimplementedOperator {
            display: format!("{:?}", op),
        }
    }
}
