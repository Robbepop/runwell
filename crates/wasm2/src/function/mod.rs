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

use crate::Error;
use ir::primitive::Func;
use module::{builders::ModuleView, FunctionBody};
use wasmparser::{FuncValidator, ValidatorResources};

pub fn translate_function_body<'a>(
    buffer: Vec<u8>,
    validator: FuncValidator<ValidatorResources>,
    func: Func,
    res: ModuleView<'a>,
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
    res: ModuleView<'b>,
}

impl<'a, 'b> FunctionBodyTranslator<'a, 'b> {
    fn translate(self) -> Result<FunctionBody, Error> {
        let builder = FunctionBody::build()
            .with_inputs(&[])?
            .with_outputs(&[])?
            .body();
        let _wasm_body = self.wasm_body;
        let _validator = self.validator;
        let _func = self.func;
        let _res = self.res;
        Ok(builder.finalize()?)
    }
}
