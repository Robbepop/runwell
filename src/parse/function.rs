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

use crate::parse::{FunctionId, Operator, ParseError};
use core::convert::TryFrom;
use derive_more::From;

/// A `runwell` type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    /// The 32-bit `i32` integer type.
    I32,
    /// The 64-bit `i64` integer type.
    I64,
}

impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
        }
    }
}

impl TryFrom<wasmparser::Type> for Type {
    type Error = ParseError;

    fn try_from(ty: wasmparser::Type) -> Result<Self, Self::Error> {
        let result = match ty {
            wasmparser::Type::I32 => Type::I32,
            wasmparser::Type::I64 => Type::I64,
            unsupported => {
                return Err(ParseError::UnsupportedType(format!(
                    "{:?}",
                    unsupported
                )))
            }
        };
        Ok(result)
    }
}

/// A function signature.
#[derive(Debug)]
pub struct FunctionSig {
    /// The input types of the function.
    inputs: Box<[Type]>,
    /// The output types of the function.
    outputs: Box<[Type]>,
}

impl TryFrom<wasmparser::FuncType> for FunctionSig {
    type Error = ParseError;

    fn try_from(func_ty: wasmparser::FuncType) -> Result<Self, Self::Error> {
        let inputs = func_ty
            .params
            .into_iter()
            .cloned()
            .map(|ty| Type::try_from(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = func_ty
            .returns
            .into_iter()
            .cloned()
            .map(|ty| Type::try_from(ty))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self::new(inputs, outputs))
    }
}

impl FunctionSig {
    /// Creates a new function signature.
    pub fn new<I, O>(inputs: I, outputs: O) -> Self
    where
        I: IntoIterator<Item = Type>,
        O: IntoIterator<Item = Type>,
    {
        Self {
            inputs: inputs.into_iter().collect::<Vec<_>>().into_boxed_slice(),
            outputs: outputs.into_iter().collect::<Vec<_>>().into_boxed_slice(),
        }
    }

    /// Returns a slice over the input types of `self`.
    pub fn inputs(&self) -> &[Type] {
        &self.inputs
    }

    /// Returns a slice over the output types of `self`.
    pub fn outputs(&self) -> &[Type] {
        &self.outputs
    }
}

/// A function.
#[derive(Debug)]
pub struct Function<'a> {
    /// The function index.
    id: FunctionId,
    /// The function signature.
    sig: &'a FunctionSig,
}

impl<'a> Function<'a> {
    /// Creates a new function from the given ID and signature.
    pub(crate) fn new(id: FunctionId, sig: &'a FunctionSig) -> Self {
        Self { id, sig }
    }

    /// Returns the function ID.
    pub fn id(&self) -> FunctionId {
        self.id
    }

    /// Returns the function signature.
    pub fn sig(&self) -> &FunctionSig {
        self.sig
    }
}

/// A function body.
#[derive(Debug, From)]
pub struct FunctionBody {
    /// The locals of the function.
    locals: Box<[(usize, Type)]>,
    /// The operations of the function.
    ops: Box<[Operator]>,
}

impl<'a> core::convert::TryFrom<wasmparser::FunctionBody<'a>> for FunctionBody {
    type Error = ParseError;

    fn try_from(
        function_body: wasmparser::FunctionBody<'a>,
    ) -> Result<Self, Self::Error> {
        let locals = function_body
            .get_locals_reader()?
            .into_iter()
            .map(|local| {
                match local {
                    Ok((num, ty)) => Ok((num as usize, Type::try_from(ty)?)),
                    Err(err) => Err(err.into()),
                }
            })
            .collect::<Result<Vec<_>, ParseError>>()?
            .into_boxed_slice();
        let ops = function_body
            .get_operators_reader()?
            .into_iter()
            .map(|op| Operator::try_from(op?))
            .collect::<Result<Vec<_>, _>>()?
            .into_boxed_slice();
        Ok(Self { locals, ops })
    }
}

impl FunctionBody {
    /// Returns the local variable declarations of the function body.
    pub fn locals(&self) -> &[(usize, Type)] {
        &self.locals
    }

    /// Returns the operations of the function body.
    pub fn ops(&self) -> &[Operator] {
        &self.ops
    }
}

mod display_impls {
    use super::*;
    use core::fmt::{Display, Formatter, Result};

    impl Display for Function<'_> {
        fn fmt(&self, f: &mut Formatter) -> Result {
            use crate::parse::Identifier as _;
            write!(f, "\nfunction {}: ", self.id().get())?;
            f.debug_list()
                .entries(self.sig().inputs().into_iter())
                .finish()?;
            write!(f, " => ")?;
            f.debug_list()
                .entries(self.sig().outputs().into_iter())
                .finish()?;
            Ok(())
        }
    }

    impl Display for FunctionBody {
        fn fmt(&self, f: &mut Formatter) -> Result {
            let ws_per_indent = 4;
            let indent_frag = " ".repeat(ws_per_indent);
            let mut indent = indent_frag.clone();

            if !self.locals().is_empty() {
                write!(f, "\nlocals")?;
                for (local_num, local_type) in self.locals() {
                    write!(f, "\n{}{} x {}", indent, local_num, local_type,)?;
                }
                write!(f, "\nend")?;
            }

            write!(f, "\nbody")?;
            for op in self.ops() {
                if let Operator::End = op {
                    for _ in 0..ws_per_indent {
                        indent.pop();
                    }
                }
                write!(f, "\n{}{}", indent, op)?;
                match op {
                    Operator::Block(_)
                    | Operator::If(_)
                    | Operator::Loop(_) => {
                        indent.push_str(&indent_frag);
                    }
                    _ => {}
                }
            }
            Ok(())
        }
    }
}
