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

#[test]
fn run_tests() {
    let input_wat = include_bytes!("pass/add.wat").to_vec();
    let input_wasm = wabt::wat2wasm(&input_wat).unwrap();
    let mut wasm_slice = &input_wasm[..];
    let parsed_wasm =
        crate::parse::parse(&mut wasm_slice, &mut Vec::new()).unwrap();
    let (fun, _body) = parsed_wasm.iter_internal_fns().next().unwrap();
    let mut translator = crate::ir::FunctionTranslator::new(&parsed_wasm);
    let translated_fn = translator.translate(fun.id());
    println!("{:#?}", translated_fn);
}
