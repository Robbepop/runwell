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
    module::FunctionSig,
    FunctionId,
    Operator,
    ParseError,
    Type,
};
use derive_more::From;

/// A Wasm function signature and its unique ID.
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
                .entries(self.sig().inputs().iter())
                .finish()?;
            write!(f, " => ")?;
            f.debug_list()
                .entries(self.sig().outputs().iter())
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
