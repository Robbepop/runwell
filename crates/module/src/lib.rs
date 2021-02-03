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

mod builder;
mod error;
mod func_body;
mod func_type;
mod global_var;
mod import_name;
mod init_expr;
mod linear_memory;
mod table;

use core::fmt;

use builder::ModuleResources;
use entity::{ComponentVec, RawIdx};
use ir::primitive::{Func, Type, Value};

pub use self::{
    builder::ModuleBuilder,
    error::{IrError, IrErrorKind},
    func_body::{
        FunctionBody,
        FunctionBuilder,
        FunctionBuilderError,
        InstructionBuilder,
        Variable,
    },
    func_type::{FunctionType, FunctionTypeBuilder},
    global_var::{Global, GlobalVariable, GlobalVariableEntity},
    import_name::ImportName,
    init_expr::InitExpr,
    linear_memory::{DataSegmentIter, LinearMemoryDecl, LinearMemoryInit},
    table::{ElementSegmentIter, TableDecl, TableInit},
};

/// A constructed and validated Runwell module.
#[derive(Debug)]
pub struct Module {
    /// The internal resources of the constructed module.
    res: ModuleResources,
    /// The bodies (implementations) of the internal functions.
    bodies: ComponentVec<Func, FunctionBody>,
}

/// A Runwell function.
///
/// Includes the function's unique index, signature and body.
///
/// This is a short-lived composite type used as merge point for
/// all information regarding a single Runwell function.
#[derive(Debug, Copy, Clone)]
pub struct Function<'a> {
    func: Func,
    func_type: &'a FunctionType,
    body: &'a FunctionBody,
}

impl<'a> Function<'a> {
    /// Returns the function's unique index.
    #[inline]
    pub fn idx(&self) -> Func {
        self.func
    }

    /// Returns the function's signature.
    #[inline]
    pub fn ty(&self) -> &'a FunctionType {
        &self.func_type
    }

    /// Returns the function's input types.
    #[inline]
    pub fn inputs(&self) -> &'a [Type] {
        self.func_type.inputs()
    }

    /// Returns the function's output types.
    #[inline]
    pub fn outputs(&self) -> &'a [Type] {
        self.func_type.outputs()
    }

    /// Returns the function body.
    #[inline]
    pub fn body(&self) -> &'a FunctionBody {
        &self.body
    }
}

impl<'a> fmt::Display for Function<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inputs = self
            .inputs()
            .iter()
            .enumerate()
            .map(|(n, ty)| {
                let val = Value::from_raw(RawIdx::from_u32(n as u32));
                (val, ty)
            })
            .collect::<Vec<_>>();
        write!(f, "{} (", self.idx())?;
        if let Some(((first_value, first_type), rest)) = inputs.split_first() {
            write!(f, "{}: {}", first_value, first_type)?;
            for (rest_value, rest_type) in rest {
                write!(f, ", {}: {}", rest_value, rest_type)?;
            }
        }
        write!(f, ")")?;
        if let Some((first_output, rest)) = self.outputs().split_first() {
            write!(f, " -> ")?;
            let just_one_output = self.outputs().len() == 1;
            if !just_one_output {
                write!(f, "[")?;
            }
            write!(f, "{}", first_output)?;
            for rest_output in rest {
                write!(f, ", {}", rest_output)?;
            }
            if !just_one_output {
                write!(f, "]")?;
            }
        }
        writeln!(f)?;
        writeln!(f, "{}", self.body())?;
        Ok(())
    }
}

impl Module {
    /// Creates a new module builder.
    pub fn build() -> ModuleBuilder {
        ModuleBuilder::new()
    }

    /// Returns the function signature and body for the given function index if any.
    pub fn get_function(&self, func: Func) -> Option<Function> {
        self.res.get_func_type(func).map(|func_type| {
            let body = &self.bodies[func];
            Function {
                func,
                func_type,
                body,
            }
        })
    }
}
