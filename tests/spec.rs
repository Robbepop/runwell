use anyhow::Result;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// A Wasm test input.
pub struct TestInput {
    /// The path to the Wasm spec testsuite file.
    ///
    /// Useful to report errors.
    pub path: PathBuf,
    /// The binary encoded Wasm module that acts as input to the tests.
    pub wasm: Vec<u8>,
}

impl TestInput {
    /// Creates a new benchmark input.
    pub fn new(test_path: PathBuf, encoded_wasm: Vec<u8>) -> Self {
        Self {
            path: test_path,
            wasm: encoded_wasm,
        }
    }
}

/// Returns a vector of all found Wasm spec testsuite input files under the given directory.
///
/// Testsuite input files can be Wasm binary format (`.wasm`),  Wasm text format (`.wat`)
/// or Wasm test format (`.wast`) formatted files.
///
/// # Note
///
/// For `.wast` files we pull out all the module directives and test them isolated.
///
/// # Errors
///
/// - If the given path is invalid.
/// - If found spec testsuite files are invalidly formatted.
fn collect_test_inputs_into(
    path: &Path,
    list: &mut Vec<TestInput>,
) -> Result<()> {
    for entry in path.read_dir()? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_test_inputs_into(&path, list)?;
            continue
        }
        match path.extension().and_then(|ext| ext.to_str()) {
            Some("wasm") => {
                let wasm = fs::read(&path)?;
                list.push(TestInput::new(path, wasm));
            }
            Some("wat") | Some("txt") => {
                if let Ok(wasm) = wat::parse_file(&path) {
                    list.push(TestInput::new(path, wasm));
                }
            }
            Some("wast") => {
                let contents = fs::read_to_string(&path)?;
                let buf = match wast::parser::ParseBuffer::new(&contents) {
                    Ok(buf) => buf,
                    Err(_) => continue,
                };
                let wast: wast::Wast<'_> = match wast::parser::parse(&buf) {
                    Ok(wast) => wast,
                    Err(_) => continue,
                };
                for directive in wast.directives {
                    match directive {
                        wast::WastDirective::Module(mut module) => {
                            let wasm = module.encode()?;
                            list.push(TestInput::new(path.clone(), wasm));
                        }
                        _ => continue,
                    }
                }
            }
            _ => (),
        }
    }
    Ok(())
}

/// Returns the default benchmark inputs that are proper `wasmparser` benchmark
/// test inputs.
fn collect_test_inputs() -> Vec<TestInput> {
    let mut ret = Vec::new();
    collect_test_inputs_into("testsuite".as_ref(), &mut ret).expect(
        "encountered problem while collecting Wasm spec testsuite inputs",
    );
    return ret
}

#[test]
fn parse_works() {
    let inputs = collect_test_inputs();
    let mut buffer = Vec::with_capacity(1000);
    let mut len_unsupported = 0;
    let mut len_failed = 0;
    let mut len_passed = 0;
    let mut local_test = 0;
    let mut last_path = PathBuf::default();
    for (n, input) in inputs.iter().enumerate() {
        if input.path != last_path {
            local_test = 0;
            last_path = input.path.clone();
        } else {
            local_test += 1;
        }
        if input.path.starts_with("testsuite/proposals") {
            // We do not take into account any proposal specific tests.
            continue
        }
        print!(
            "  test {:4}: {}/{}: ",
            n,
            input.path.file_stem().unwrap().to_str().unwrap(),
            local_test
        );
        let result = runwell::parse::parse(&mut &input.wasm[..], &mut buffer);
        match result {
            Ok(_) => {
                println!("ok");
                len_passed += 1;
            }
            Err(error) => {
                if error.is_unsupported_error() {
                    println!("unsupported {:?}", error);
                    len_unsupported += 1;
                } else {
                    println!("FAILED {:?}", error);
                    len_failed += 1;
                }
            }
        }
    }
    println!(
        "\n\
        # tests passed:      {:4}\n\
        # tests failed:      {:4}\n\
        # tests unsupported: {:4}\n\
    ",
        len_passed, len_failed, len_unsupported
    );
    assert_eq!(len_failed, 0);
}

#[test]
fn parse2_works() {
    let inputs = collect_test_inputs();
    let mut buffer = Vec::with_capacity(1000);
    let mut len_failed = 0;
    let mut len_passed = 0;
    let mut local_test = 0;
    let mut last_path = PathBuf::default();
    for (n, input) in inputs.iter().enumerate() {
        if input.path != last_path {
            local_test = 0;
            last_path = input.path.clone();
        } else {
            local_test += 1;
        }
        if input.path.starts_with("testsuite/proposals") {
            // We do not take into account any proposal specific tests.
            continue
        }
        print!(
            "  test {:4}: {}/{}: ",
            n,
            input.path.file_stem().unwrap().to_str().unwrap(),
            local_test
        );
        let result = runwell::parse2::parse(&mut &input.wasm[..], &mut buffer);
        match result {
            Ok(_) => {
                println!("ok");
                len_passed += 1;
            }
            Err(error) => {
                println!("FAILED {:?}", error);
                len_failed += 1;
            }
        }
    }
    println!(
        "\n\
        # tests passed:      {:4}\n\
        # tests failed:      {:4}\n\
    ",
        len_passed, len_failed
    );
    assert_eq!(len_failed, 0);
}