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
