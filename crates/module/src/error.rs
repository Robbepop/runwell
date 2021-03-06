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
use derive_more::{Display, Error, From};

pub use super::{
    func_body::FunctionBuilderError,
    store::{GlobalError, MemoryError, StoreError, Trap, TrapCode},
};

/// An error that occurred while translating from Wasm to Runwell IR.
#[derive(Debug, Error, From, PartialEq, Eq)]
pub struct Error {
    kind: ErrorKind,
    context: Vec<String>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)?;
        if let Some((first, rest)) = self.context.split_first() {
            writeln!(f, "\n  context: {}", first)?;
            for context in rest {
                writeln!(f, "           {}", context)?;
            }
        }
        Ok(())
    }
}

impl Error {
    /// Constructs a new IR error from the given error kind.
    fn from_kind(kind: ErrorKind) -> Self {
        Self {
            kind,
            context: Vec::new(),
        }
    }

    /// Adds context information to the current error.
    pub fn with_context<T>(mut self, context: T) -> Self
    where
        T: Into<String>,
    {
        self.context.push(context.into());
        self
    }

    /// Returns a shared reference to the underlying kind of encountered error.
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }
}

impl From<FunctionBuilderError> for Error {
    fn from(error: FunctionBuilderError) -> Self {
        Self::from_kind(error.into())
    }
}

/// An error kind that occurred while translating from Wasm to Runwell IR.
#[derive(Debug, Display, Error, From, PartialEq, Eq)]
pub enum ErrorKind {
    FunctionBuilder(FunctionBuilderError),
}
