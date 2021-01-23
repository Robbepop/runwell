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

// pub mod builder;
mod error;
mod export;
mod function;
mod global;
mod import;
mod index;
mod initializer;
mod memory;
mod primitive;
mod read;
mod section;
mod signature;
mod table;

pub use self::{
    error::{ParseError, ParseErrorKind},
    export::{Export, ExportError, ExportItem},
    function::{
        FunctionBody,
        LocalVariableEntry,
        LocalsIter,
        OperatorsIter,
        OriginalPosition,
    },
    global::GlobalVariable,
    import::{ImportError, ImportName},
    index::{
        FunctionId,
        FunctionTypeId,
        GlobalVariableId,
        LinearMemoryId,
        TableId,
    },
    initializer::{InitializerExpr, InitializerExprError},
    memory::{Data, LinearMemory, MemoryError},
    primitive::{PrimitiveError, Type, Value, F32, F64},
    read::{Read, ReadError},
    section::{parse, SectionError},
    signature::FunctionType,
    table::{Element, ElementItemsIter, Table, TableError},
};
