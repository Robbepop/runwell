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

use std::convert::TryInto;

use super::{
    BuilderError,
    FunctionBody,
    Data,
    Export,
    FunctionId,
    FunctionSigId,
    GlobalVariable,
    ImportError,
    ImportName,
    Index32,
    LinearMemory,
    ModuleBuilder,
    ParseError,
    Read,
    ReadError,
    Table,
};
use core::convert::TryFrom;
use derive_more::{Display, Error};
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
    Parser,
    Payload,
    TableSectionReader,
    TypeSectionReader,
    Validator,
};

/// A general error that might occure while parsing Wasm sections.
#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum SectionError {
    Unsupported(UnsupportedWasmSection),
    UnsupportedTypeDef(UnsupportedTypeDef),
}

#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum UnsupportedWasmSection {
    #[display(fmt = "encountered unsupported Wasm module section")]
    Module,
    #[display(fmt = "encountered unsupported Wasm instance section")]
    Instance,
    #[display(fmt = "encountered unsupported Wasm alias section")]
    Alias,
    #[display(fmt = "encountered unsupported Wasm event section")]
    Event,
    #[display(fmt = "encountered unsupported unknown Wasm section")]
    Unknown,
}

#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum UnsupportedTypeDef {
    #[display(fmt = "encountered unsupported Wasm type def: instance")]
    Instance,
    #[display(fmt = "encountered unsupported Wasm type def: module")]
    Module,
}

pub fn parse<B, R>(
    mut reader: R,
    buf: &mut Vec<u8>,
) -> Result<<B as ModuleBuilder>::Module, ParseError>
where
    B: ModuleBuilder + Default,
    R: Read,
{
    let mut parser = Parser::new(0);
    let mut eof = false;
    let mut module = B::default();
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
    let finalized = module.finalize().map_err(|_| BuilderError {})?;
    Ok(finalized)
}

/// Validates the payload and feeds it into the module.
///
/// Returns `true` if payload is the end section.
fn process_payload<B>(
    payload: Payload,
    module: &mut B,
    validator: &mut Validator,
) -> Result<bool, ParseError>
where
    B: ModuleBuilder,
{
    match payload {
        Payload::Version { num, range } => {
            validator.version(num, &range)?;
        }
        Payload::TypeSection(section_reader) => {
            parse_type_section(section_reader, module, validator)?;
        }
        Payload::ImportSection(section_reader) => {
            parse_import_section(section_reader, module, validator)?;
        }
        Payload::FunctionSection(section_reader) => {
            parse_function_section(section_reader, module, validator)?;
        }
        Payload::TableSection(section_reader) => {
            parse_table_section(section_reader, module, validator)?;
        }
        Payload::MemorySection(section_reader) => {
            parse_linear_memory_section(section_reader, module, validator)?;
        }
        Payload::GlobalSection(section_reader) => {
            parse_globals_section(section_reader, module, validator)?;
        }
        Payload::ExportSection(section_reader) => {
            parse_export_section(section_reader, module, validator)?;
        }
        Payload::StartSection { func, range } => {
            parse_start_fn(func, range, module, validator)?;
        }
        Payload::ElementSection(section_reader) => {
            parse_element_section(section_reader, module, validator)?;
        }
        Payload::CodeSectionStart {
            count,
            range,
            size: _,
        } => {
            parse_code_start_section(count, range, module, validator)?;
        }
        Payload::CodeSectionEntry(body) => {
            parse_code_section(body, module, validator)?;
        }
        Payload::DataCountSection { count, range } => {
            parse_data_count_section(count, range, module, validator)?;
        }
        Payload::DataSection(section_reader) => {
            parse_data_section(section_reader, module, validator)?;
        }

        Payload::AliasSection(_)
        | Payload::InstanceSection(_)
        | Payload::ModuleSection(_)
        | Payload::ModuleCodeSectionStart { .. }
        | Payload::ModuleCodeSectionEntry { .. } => {
            return Err(SectionError::Unsupported(
                UnsupportedWasmSection::Module,
            ))
            .map_err(Into::into)
        }
        Payload::EventSection(_) => {
            return Err(SectionError::Unsupported(UnsupportedWasmSection::Event))
                .map_err(Into::into)
        }

        Payload::CustomSection {
            name: _,
            data_offset: _,
            data: _,
        } => { /* custom sections are ignored */ }
        Payload::UnknownSection {
            id: _,
            contents: _,
            range: _,
        } => {
            return Err(SectionError::Unsupported(
                UnsupportedWasmSection::Unknown,
            ))
            .map_err(Into::into)
        }

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
fn parse_type_section<B>(
    reader: TypeSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.type_section(&reader)?;
    let count = reader.get_count();
    module.reserve_types(count)?;
    for type_def in reader {
        match type_def? {
            wasmparser::TypeDef::Func(func_type) => {
                let fn_sig = func_type.try_into()?;
                module.define_type(fn_sig)?;
            }
            wasmparser::TypeDef::Instance(_) => {
                return Err(SectionError::UnsupportedTypeDef(
                    UnsupportedTypeDef::Instance,
                ))
                .map_err(Into::into)
            }
            wasmparser::TypeDef::Module(_) => {
                return Err(SectionError::UnsupportedTypeDef(
                    UnsupportedTypeDef::Module,
                ))
                .map_err(Into::into)
            }
        }
    }
    Ok(())
}

/// Validates the Wasm `imports` section and feeds its contents into the `module`.
///
/// The imports in the `module` are going to be separated for each kind.
///
/// # Errors
///
/// - If the `reader` yields an invalid Wasm type section.
/// - If the `reader` yields unsupported module import definitions.
fn parse_import_section<B>(
    reader: ImportSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.import_section(&reader)?;
    for import in reader {
        let import = import?;
        let module_name = import.module;
        let field_name = import.field;
        let import_name =
            ImportName::new(module_name, field_name.unwrap_or_default());
        match import.ty {
            ImportSectionEntryType::Function(fn_sig_id) => {
                module.import_function(
                    import_name,
                    FunctionSigId::from_u32(fn_sig_id),
                )?
            }
            ImportSectionEntryType::Table(table_type) => {
                module
                    .import_table(import_name, Table::try_from(table_type)?)?;
            }
            ImportSectionEntryType::Memory(memory_type) => {
                module.import_memory(
                    import_name,
                    LinearMemory::try_from(memory_type)?,
                )?;
            }
            ImportSectionEntryType::Global(global_type) => {
                module.import_global(
                    import_name,
                    GlobalVariable::try_from(global_type)?,
                )?;
            }
            ImportSectionEntryType::Module(_)
            | ImportSectionEntryType::Instance(_) => {
                return Err(ImportError::UnsupportedModuleImport)
                    .map_err(Into::into)
            }
            ImportSectionEntryType::Event(_) => {
                return Err(ImportError::UnsupportedEventImport)
                    .map_err(Into::into)
            }
        }
    }
    Ok(())
}

fn parse_function_section<B>(
    reader: FunctionSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.function_section(&reader)?;
    let total_count = reader.get_count();
    module.reserve_functions(total_count)?;
    for fn_sig in reader {
        let fn_sig_id = fn_sig?;
        module.declare_function(FunctionSigId::from_u32(fn_sig_id))?;
    }
    Ok(())
}

fn parse_table_section<B>(
    reader: TableSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.table_section(&reader)?;
    let total_count = reader.get_count();
    module.reserve_tables(total_count)?;
    for table_type in reader {
        let table_type = table_type?;
        module.declare_table(Table::try_from(table_type)?)?;
    }
    Ok(())
}

fn parse_linear_memory_section<B>(
    reader: MemorySectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.memory_section(&reader)?;
    let total_count = reader.get_count();
    module.reserve_memories(total_count)?;
    for memory_type in reader {
        let memory_type = memory_type?;
        module.declare_memory(LinearMemory::try_from(memory_type)?)?;
    }
    Ok(())
}

fn parse_globals_section<B>(
    reader: GlobalSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.global_section(&reader)?;
    let total_count = reader.get_count();
    module.reserve_globals(total_count)?;
    for global in reader {
        let global = global?;
        let global_type = GlobalVariable::try_from(global.ty)?;
        let global_init = global.init_expr.try_into()?;
        module.define_global(global_type, global_init)?;
    }
    Ok(())
}

fn parse_export_section<B>(
    reader: ExportSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.export_section(&reader)?;
    for export in reader {
        let export = export?;
        let export = Export::try_from(export)?;
        module.declare_export(export);
    }
    Ok(())
}

fn parse_start_fn<B>(
    start_fn_id: u32,
    range: wasmparser::Range,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.start_section(start_fn_id, &range)?;
    module.set_start_fn(FunctionId::from_u32(start_fn_id));
    Ok(())
}

fn parse_element_section<B>(
    reader: ElementSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.element_section(&reader)?;
    let total_count = reader.get_count();
    module.reserve_elements(total_count)?;
    for element in reader {
        let element = element?.try_into()?;
        module.define_element(element)?;
    }
    Ok(())
}

fn parse_code_start_section<B>(
    count: u32,
    range: wasmparser::Range,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.code_section_start(count, &range)?;
    module.reserve_function_bodies(count)?;
    Ok(())
}

fn parse_code_section<B>(
    body: wasmparser::FunctionBody,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    let mut fn_validator = validator.code_section_entry()?;
    let fn_body = FunctionBody::new(&mut fn_validator, body)?;
    module.define_function_body(fn_body)?;
    Ok(())
}

fn parse_data_count_section<B>(
    count: u32,
    range: wasmparser::Range,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.data_count_section(count, &range)?;
    module.reserve_datas(count)?;
    Ok(())
}

fn parse_data_section<B>(
    reader: DataSectionReader,
    module: &mut B,
    validator: &mut Validator,
) -> Result<(), ParseError>
where
    B: ModuleBuilder,
{
    validator.data_section(&reader)?;
    let total_count = reader.get_count();
    module.reserve_datas(total_count)?;
    for data in reader {
        let data = data?;
        let data = Data::try_from(data)?;
        module.define_data(data)?;
    }
    Ok(())
}
