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
    module::Data,
    FunctionId,
    FunctionSigId,
    Module,
    ModuleBuilder,
    ParseError,
};
use core::convert::TryInto as _;
use derive_more::Display;
use std::convert::TryFrom;
use wasmparser::{
    Chunk,
    DataSectionReader,
    ElementSectionReader,
    ExportSectionReader,
    FunctionSectionReader,
    GlobalSectionReader,
    ImportSectionEntryType,
    ImportSectionReader,
    MemorySectionReader,
    Parser as WasmParser,
    Payload,
    Range as WasmRange,
    TableSectionReader,
    TypeSectionReader,
    Validator,
};

use super::FunctionBody;

/// Errors returned by [`Read::read`].
#[derive(Debug, Display)]
pub enum ReadError {
    /// The source has reached the end of the stream.
    #[display(fmt = "encountered unexpected end of stream")]
    EndOfStream,
    /// An unknown error occurred.
    #[display(fmt = "encountered unknown read error")]
    UnknownError,
}

/// The Read trait allows for reading bytes from a source.
///
/// # Note
///
/// Provides a subset of the interface provided by Rust's [`std::io::Read`][std_io_read] trait.
///
/// [std_io_read]: https://doc.rust-lang.org/std/io/trait.Read.html
pub trait Read {
    /// Pull some bytes from this source into the specified buffer, returning how many bytes were read.
    ///
    /// # Note
    ///
    /// Provides the same guarantees to the caller as [`std::io::Read::read`][io_read_read].
    ///
    /// [io_read_read]: https://doc.rust-lang.org/std/io/trait.Read.html#tymethod.read
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ReadError>;
}

#[cfg(feature = "std")]
impl<T> Read for T
where
    T: ::std::io::Read,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ReadError> {
        <T as ::std::io::Read>::read(self, buf).map_err(|err| {
            match err.kind() {
                ::std::io::ErrorKind::UnexpectedEof => ReadError::EndOfStream,
                _ => ReadError::UnknownError,
            }
        })
    }
}

#[cfg(not(feature = "std"))]
impl<'a> Read for &'a [u8] {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, ReadError> {
        let len_copy = core::cmp::min(self.len(), buf.len());
        buf.copy_from_slice(&self[..len_copy]);
        *self = &self[len_copy..];
        Ok(len_copy)
    }
}

pub fn parse<R>(mut reader: R, buf: &mut Vec<u8>) -> Result<Module, ParseError>
where
    R: Read,
{
    let mut parser = WasmParser::new(0);
    let mut eof = false;
    let mut module = Module::build();
    let mut validator = Validator::default();
    buf.clear();
    loop {
        match parser.parse(&buf, eof)? {
            Chunk::NeedMoreData(hint) => {
                assert!(!eof); // Otherwise an error would be returned by `parse`.

                // Use the hint to preallocate more space, then read
                // some more data into the buffer.
                //
                // Note that the buffer management here is not ideal,
                // but it's compact enough to fit in an example!
                let len = buf.len();
                buf.extend((0..hint).map(|_| 0u8));
                let n = reader
                    .read(&mut buf[len..])
                    .map_err(|_| ReadError::UnknownError)?;
                buf.truncate(len + n);
                eof = n == 0;
                continue
            }
            Chunk::Parsed { consumed, payload } => {
                let end_section =
                    process_payload(payload, &mut module, &mut validator)?;
                // Cut away the parts from the intermediate buffer that have already been parsed.
                buf.drain(..consumed);
                if end_section {
                    break
                }
            }
        };
    }
    let finalized = module.finalize()?;
    Ok(finalized)
}

/// Validates the payload and feeds it into the module.
///
/// Returns `true` if payload is the end section.
fn process_payload<'a>(
    payload: Payload,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<bool, ParseError> {
    match payload {
        Payload::Version { num, range } => {
            validator.version(num, &range)?;
        }
        Payload::TypeSection(section_reader) => {
            parse_types(section_reader, module, validator)?;
        }
        Payload::ImportSection(section_reader) => {
            parse_imports(section_reader, module, validator)?;
        }
        Payload::FunctionSection(section_reader) => {
            parse_function_signatures(section_reader, module, validator)?;
        }
        Payload::TableSection(section_reader) => {
            parse_tables(section_reader, module, validator)?;
        }
        Payload::MemorySection(section_reader) => {
            parse_linear_memories(section_reader, module, validator)?;
        }
        Payload::GlobalSection(section_reader) => {
            parse_globals(section_reader, module, validator)?;
        }
        Payload::ExportSection(section_reader) => {
            parse_exports(section_reader, module, validator)?;
        }
        Payload::StartSection { func, range } => {
            parse_start(func, range, module, validator)?;
        }
        Payload::ElementSection(section_reader) => {
            parse_element(section_reader, module, validator)?;
        }
        Payload::CodeSectionStart {
            count,
            range,
            size: _,
        } => {
            parse_code_start(count, range, module, validator)?;
        }
        Payload::CodeSectionEntry(body) => {
            parse_fn_body(body, module, validator)?;
        }
        Payload::DataCountSection { count, range } => {
            parse_data_count(count, range, module, validator)?;
        }
        Payload::DataSection(section_reader) => {
            parse_data(section_reader, module, validator)?;
        }

        Payload::AliasSection(_)
        | Payload::InstanceSection(_)
        | Payload::ModuleSection(_)
        | Payload::ModuleCodeSectionStart { .. }
        | Payload::ModuleCodeSectionEntry { .. } => {
            return Err(ParseError::UnsupportedModuleDefinition)
        }

        Payload::CustomSection {
            name: _,
            data_offset: _,
            data: _,
        } => { /* ... */ }
        Payload::UnknownSection {
            id: _,
            contents: _,
            range: _,
        } => { /* ... */ }

        Payload::End => return Ok(true),
    }
    Ok(false)
}

/// Validates the Wasm `type` section and feeds its contents into the `module`.
///
/// # Errors
///
/// - If the `reader` yields an invalid Wasm type section.
/// - If the `reader` yields unsupported module or instance definitions.
fn parse_types(
    reader: TypeSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.type_section(&reader)?;
    let count = reader.get_count();
    module.reserve_fn_signatures(count as usize)?;
    for type_def in reader.into_iter() {
        match type_def? {
            wasmparser::TypeDef::Func(func_type) => {
                let fn_sig = func_type.try_into()?;
                module.register_fn_signature(fn_sig)?;
            }
            wasmparser::TypeDef::Instance(_) => {
                return Err(ParseError::UnsupportedInstanceDefinition)
            }
            wasmparser::TypeDef::Module(_) => {
                return Err(ParseError::UnsupportedModuleDefinition)
            }
        }
    }
    Ok(())
}

fn parse_imports(
    reader: ImportSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.import_section(&reader)?;
    for import in reader.into_iter() {
        let import = import?;
        let module_name = import.module;
        let field_name = import.field;
        match import.ty {
            ImportSectionEntryType::Function(fn_sig_id) => {
                module.push_imported_fn(
                    module_name,
                    field_name.unwrap_or(""),
                    FunctionSigId(fn_sig_id as usize),
                )?
            }
            ImportSectionEntryType::Table(table_type) => {
                module.push_imported_table(
                    module_name,
                    field_name.unwrap_or(""),
                    table_type,
                )?;
            }
            ImportSectionEntryType::Memory(memory_type) => {
                module.push_imported_linear_memory(
                    module_name,
                    field_name.unwrap_or(""),
                    memory_type,
                )?;
            }
            ImportSectionEntryType::Global(global_type) => {
                module.push_imported_global(
                    module_name,
                    field_name.unwrap_or(""),
                    global_type.into(),
                )?;
            }
            ImportSectionEntryType::Module(_)
            | ImportSectionEntryType::Instance(_) => {
                return Err(ParseError::UnsupportedModuleDefinition)
            }
        }
    }
    Ok(())
}

fn parse_function_signatures(
    reader: FunctionSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.function_section(&reader)?;
    for fn_sig in reader.into_iter() {
        module.push_internal_fn(FunctionSigId(fn_sig? as usize))
    }
    Ok(())
}

fn parse_tables(
    reader: TableSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.table_section(&reader)?;
    for table_type in reader.into_iter() {
        module.push_internal_table(table_type?)
    }
    Ok(())
}

fn parse_linear_memories(
    reader: MemorySectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.memory_section(&reader)?;
    for memory_type in reader.into_iter() {
        module.push_internal_linear_memory(memory_type?)
    }
    Ok(())
}

fn parse_globals(
    reader: GlobalSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.global_section(&reader)?;
    for global_type in reader.into_iter() {
        let global_type = global_type?;
        module.push_internal_global(global_type.ty.into());
        module.push_global_initializer(global_type.init_expr.try_into()?);
    }
    Ok(())
}

fn parse_exports(
    reader: ExportSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.export_section(&reader)?;
    for export in reader.into_iter() {
        module.push_export(export?.into());
    }
    Ok(())
}

fn parse_start(
    start_fn_id: u32,
    range: WasmRange,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.start_section(start_fn_id, &range)?;
    module.set_start_fn(FunctionId(start_fn_id as usize));
    Ok(())
}

fn parse_element(
    reader: ElementSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.element_section(&reader)?;
    for element in reader.into_iter() {
        module.push_element(element?.try_into()?)
    }
    Ok(())
}

fn parse_code_start(
    count: u32,
    range: WasmRange,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.code_section_start(count, &range)?;
    module.reserve_fn_bodies(count as usize)?;
    Ok(())
}

fn parse_fn_body(
    body: wasmparser::FunctionBody,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    let mut fn_validator = validator.code_section_entry()?;
    let mut reader = body.get_binary_reader();
    fn_validator.read_locals(&mut reader)?;
    while !reader.eof() {
        let pos = reader.original_position();
        let op = reader.read_operator()?;
        fn_validator.op(pos, &op)?;
    }
    let fn_body = FunctionBody::try_from(body)?;
    module.push_fn_body(fn_body)?;
    Ok(())
}

fn parse_data_count(
    count: u32,
    range: WasmRange,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.data_count_section(count, &range)?;
    module.reserve_data_elements(count as usize)?;
    Ok(())
}

fn parse_data(
    reader: DataSectionReader,
    module: &mut ModuleBuilder,
    validator: &mut Validator,
) -> Result<(), ParseError> {
    validator.data_section(&reader)?;
    for data in reader.into_iter() {
        let data = data?;
        module.push_data(Data::from(data))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_incrementer() {
        let wasm = include_bytes!("../../incrementer.wasm");
        let module = parse(&mut &wasm[..], &mut Vec::new())
            .expect("invalid Wasm byte code");
        for (fn_sig, fn_body) in module.iter_internal_fns().skip(165).take(1) {
            println!("{}{}", fn_sig, fn_body);
        }
    }
}
