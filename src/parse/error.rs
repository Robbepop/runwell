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

use derive_more::{Display, From};
use thiserror::Error;

/// An error that can be encountered upon parsing a Wasm module.
#[derive(Debug, Display, From)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum ParseError {
    /// An error encountered in the underlying parser.
    #[display(fmt = "encountered parser error")]
    Parser(wasmparser::BinaryReaderError),
    /// Encountered upon unmatching function declarations and definitions.
    #[display(fmt = "unmatching fn declarations and definitions")]
    UnmatchingFnDeclToDef,
    /// Encountered upon encountering multiple memory section entries.
    #[display(fmt = "multiple memory entries are unsupported, yet")]
    MultipleMemoriesUnsupported,
    /// Missing a linear memory section or entry.
    #[display(fmt = "missing linear memory section or entry")]
    MissingMemoryEntry,
    /// Min-max linear memory section does not match.
    #[display(fmt = "unmatching minimum and maximum linear memory limits")]
    UnmatchingMinMaxMemoryLimits,
    /// Imported entity encountered after internal one.
    #[display(fmt = "encountered imported entitiy after internal one")]
    ImportedEntityAfterInternal,
}
