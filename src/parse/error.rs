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
    module::{
        BuildError,
        EvaluationError,
        ExportError,
        MemoryError,
        ModuleError,
        TypesError,
    },
    ReadError,
};
use derive_more::{Display, From};
use thiserror::Error;

#[derive(Debug, Display)]
pub enum UnsupportedWasmSection {
    #[display(fmt = "encountered unsupported Wasm module section")]
    Module,
    #[display(fmt = "encountered unsupported Wasm instance section")]
    Instance,
    #[display(fmt = "encountered unsupported Wasm alias section")]
    Alias,
    #[display(fmt = "encountered unsupported Wasm event section")]
    Event,
    #[display(fmt = "encountered unsupported Wasm custom section")]
    Custom,
    #[display(fmt = "encountered unsupported unknown Wasm section")]
    Unknown,
}

#[derive(Debug, Display)]
pub enum ImportError {
    #[display(fmt = "encountered unsupported Wasm module import")]
    UnsupportedModuleImport,
    #[display(fmt = "encountered unsupported Wasm event import")]
    UnsupportedEventImport,
}

impl ImportError {
    /// Returns `true` if the error states that some unsupported Wasm definition has been encountered.
    pub fn is_unsupported_error(&self) -> bool {
        match self {
            Self::UnsupportedModuleImport | Self::UnsupportedEventImport => {
                true
            }
        }
    }
}

/// An error that can be encountered upon parsing a Wasm module.
#[derive(Debug, Display, From)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum CompilerError {
    /// An error that occured upon operating with the Wasm type table.
    Types(TypesError),
    /// An error that might occure upon exporting items.
    Export(ExportError),
    Import(ImportError),
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
    UnsupportedWasmSection(UnsupportedWasmSection),
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
    #[display(fmt = "encountered unsupported null element item")]
    UnsupportedNullElementItem,
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

impl CompilerError {
    /// Returns `true` if the error states that some unsupported Wasm definition has been encountered.
    pub fn is_unsupported_error(&self) -> bool {
        match self {
            Self::UnsupportedWasmSection(_)
            | Self::MultipleMemoriesUnsupported
            | Self::UnsupportedPassiveElement
            | Self::UnsupportedDeclaredElement
            | Self::UnsupportedElementKind
            | Self::UnsupportedOperator(_)
            | Self::UnsupportedNullElementItem
            | Self::UnsupportedType(_) => true,
            Self::Types(error) => error.is_unsupported_error(),
            Self::Import(error) => error.is_unsupported_error(),
            Self::Export(error) => error.is_unsupported_error(),
            Self::Memory(error) => error.is_unsupported_error(),
            Self::GlobalInit(error) => error.is_unsupported_error(),
            _ => false,
        }
    }
}
