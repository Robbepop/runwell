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

//! Utilities to translate a Wasm function body into a Runwell function body.

use crate::{Error, Type};
use core::convert::TryFrom as _;
use ir::primitive::Func;
use module::{FunctionBody, ModuleResources};
use wasmparser::{FuncValidator, ValidatorResources};

pub fn translate_function_body(
    buffer: Vec<u8>,
    validator: FuncValidator<ValidatorResources>,
    func: Func,
    res: &ModuleResources,
) -> Result<FunctionBody, Error> {
    let wasm_body = wasmparser::FunctionBody::new(0, &buffer[..]);
    let translator = FunctionBodyTranslator {
        wasm_body,
        validator,
        func,
        res,
    };
    translator.translate()
}

/// Translates Wasm function bodies into Runwell function bodies.
pub struct FunctionBodyTranslator<'a, 'b> {
    // The Wasm function body.
    wasm_body: wasmparser::FunctionBody<'a>,
    /// Used to validate a function on the fly during translation.
    validator: FuncValidator<ValidatorResources>,
    /// The unique function index associated to the translated function body.
    func: Func,
    /// The immutable module resources required to translate the function body.
    res: &'b ModuleResources,
}

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    fn translate(self) -> Result<FunctionBody, Error> {
        let Self {
            wasm_body,
            mut validator,
            func,
            res,
        } = self;
        let func_type = res
            .get_func_type(func)
            .expect("encountered invalid function reference");
        let mut builder = FunctionBody::build()
            .with_inputs(func_type.inputs())?
            .with_outputs(func_type.outputs())?;
        let mut reader = wasm_body.get_binary_reader();
        let count_locals = reader.read_var_u32()?;
        for _ in 0..count_locals {
            let offset = reader.original_position();
            let count = reader.read_var_u32()?;
            let ty = reader.read_type()?;
            validator.define_locals(offset, count, ty)?;
            let ty = Type::try_from(ty)?.into_inner();
            builder.declare_variables(count, ty)?;
        }
        let builder = builder.body();
        Ok(builder.finalize()?)
    }
}
