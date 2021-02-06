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

#![forbid(unsafe_code)]

mod error;
mod export;
mod func_type;
mod function;
mod global;
mod import;
mod init_expr;
mod memory;
mod primitive;
mod read;
mod section;
mod table;

pub use self::{
    error::{Error, ErrorKind},
    export::{Export, ExportError, ExportItem, ExportKind},
    func_type::FunctionType,
    function::{
        TranslateError,
        FunctionBodyTranslator,
    },
    global::GlobalVariable,
    import::{ImportError, ImportName},
    init_expr::{InitExpr, InitExprError},
    memory::{LinearMemoryDecl, MemoryDataInit, MemoryError},
    primitive::{PrimitiveError, Type, Value},
    read::{Read, ReadError},
    section::{
        parse,
        SectionError,
        UnexpectedWasmPayload,
        UnsupportedTypeDef,
        UnsupportedWasmSection,
    },
    table::{TableDecl, TableError},
};
