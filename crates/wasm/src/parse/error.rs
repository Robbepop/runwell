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

use super::{
    ExportError,
    ImportError,
    InitializerExprError,
    MemoryError,
    PrimitiveError,
    ReadError,
    SectionError,
    TableError,
};
use crate::builder::BuilderError;
use core::fmt::Display;
use derive_more::{Display, Error, From};

/// An error that occured while parsing a Wasm input and building up the module for it.
#[derive(Debug, Error)]
pub struct ParseError {
    /// The range of bytes in the input Wasm binary that is associated to this error.
    span: Option<Span>,
    /// Additional context to the error.
    context: String,
    /// The kind of the error holding valuable information to the user.
    kind: ParseErrorKind,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "encountered error while parsing Wasm file")?;
        if let Some(span) = &self.span {
            write!(f, " at {}", span)?;
        }
        write!(f, ". context: {}. error: {}", self.context, self.kind)?;
        Ok(())
    }
}

impl ParseError {
    /// Sets or overwrites the span of the error.
    pub fn set_span(&mut self, span: Span) {
        self.span = Some(span);
    }

    /// Sets or overwrites the span of the error and returns `self`.
    pub fn with_span(mut self, span: Span) -> Self {
        self.set_span(span);
        self
    }

    /// Sets or overwrites the context of the error.
    pub fn set_context<S>(&mut self, context: S)
    where
        S: Into<String>,
    {
        self.context = context.into();
    }

    /// Sets or overwrites the context of the error and returns `self`.
    pub fn with_context<S>(mut self, context: S) -> Self
    where
        S: Into<String>,
    {
        self.set_context(context);
        self
    }
}

/// Span denoting the range of bytes in a Wasm binary input that is associated to some error.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// The inclusive start of the byte range.
    start: usize,
    /// The non-inclusive end of the byte range.
    end: usize,
}

impl From<wasmparser::Range> for Span {
    fn from(range: wasmparser::Range) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl<E> From<E> for ParseError
where
    E: Into<ParseErrorKind>,
{
    fn from(error: E) -> Self {
        Self {
            span: None,
            context: String::new(),
            kind: error.into(),
        }
    }
}

/// Any kind of error that might occure while parsing a Wasm input binary.
#[derive(Debug, Display, Error, From)]
pub enum ParseErrorKind {
    Primitive(PrimitiveError),
    Import(ImportError),
    Export(ExportError),
    InitializerExpr(InitializerExprError),
    Memory(MemoryError),
    Table(TableError),
    Read(ReadError),
    Section(SectionError),
    Builder(BuilderError),
    Wasmparser(wasmparser::BinaryReaderError),
}
