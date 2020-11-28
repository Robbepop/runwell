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
    initializer::GlobalInitError,
    module::{BuildError, ModuleError, MemoryError, EvaluationError},
    ReadError,
};
use derive_more::{Display, From};
use thiserror::Error;

/// An error that can be encountered upon parsing a Wasm module.
#[derive(Debug, Display, From)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum ParseError {
    /// An error upon building up data structures for the module.
    Module(ModuleError),
    /// An error upon evaluating initializer expressions.
    Evaluation(EvaluationError),
    /// An error upon interacting with linear memory.
    Memory(MemoryError),
    /// An error upon parsing a global initializer expression.
    GlobalInit(GlobalInitError),
    /// An error while reading from the input.
    Read(ReadError),
    /// An error while building up the Wasm module.
    Build(BuildError),
    /// An error encountered in the underlying parser.
    #[display(fmt = "encountered parser error")]
    Parser(wasmparser::BinaryReaderError),
    /// Encountered upon encountering a module section in the input.
    #[display(fmt = "encountered unsupported module section")]
    UnsupportedModuleSection,
    #[display(fmt = "encountered unsupported module definition")]
    UnsupportedModuleDefinition,
    #[display(fmt = "encountered unsupported instance definition")]
    UnsupportedInstanceDefinition,
    #[display(fmt = "encountered unsupported event definition")]
    UnsupportedEventDefinition,
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
    /// Unsupported passive element.
    #[display(fmt = "encountered unsupported passive element")]
    UnsupportedPassiveElement,
    /// Unsupported declared element.
    #[display(fmt = "encountered unsupported declared element")]
    UnsupportedDeclaredElement,
    /// Unsupported element kind (Null).
    #[display(fmt = "encountered unsupported null element kind")]
    UnsupportedElementKind,
    #[display(fmt = "encountered invalid or unsupported element item")]
    InvalidElementItem,
    /// Encountered unsupported Wasm operator.
    #[display(fmt = "encountered unsupported Wasm operator: {}", self.0)]
    // We only store the string representation of the unsupported operator
    // instead of storing the real `wasmparser::Operator` that caused the
    // error because it would introduce a lifetime that we do not want at
    // this point.
    #[from(ignore)]
    UnsupportedOperator(String),
    /// Encountered invalid extension Wasm operator.
    #[display(fmt = "encountered invalid extension Wasm operator")]
    ExtensionToSmallerInt,
    /// Encountered invalid truncation Wasm operator.
    #[display(fmt = "encountered invalid truncation Wasm operator")]
    TruncationToBiggerInt,
    /// Encountered an unsupported Wasm type.
    #[display(fmt = "encountered unsupported Wasm type: {:?}", self.0)]
    #[from(ignore)]
    UnsupportedType(String),
}
