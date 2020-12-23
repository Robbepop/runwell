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

use super::{
    Data,
    Export,
    FunctionBody,
    FunctionId,
    FunctionSigId,
    GlobalVariable,
    ImportError,
    ImportName,
    Index32,
    LinearMemory,
    ParseError,
    Read,
    Table,
};
use crate::builder::{Module, ModuleBuilder};
use core::convert::TryFrom;
use derive_more::{Display, Error};
use std::convert::TryInto;
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
    #[display(fmt = "encountered unsupported Wasm data count section")]
    DataCount,
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

pub fn parse<R>(
    mut reader: R,
    buffer: &mut Vec<u8>,
) -> Result<Module, ParseError>
where
    R: Read,
{
    let mut parser = Parser::new(0);
    let mut eof = false;
    let mut context = ParseContext::default();
    buffer.clear();
    loop {
        match parser.parse(&buffer, eof)? {
            Chunk::NeedMoreData(hint) => {
                assert!(!eof); // Otherwise an error would be returned by `parse`.

                // Use the hint to preallocate more space, then read
                // some more data into the buffer.
                //
                // Note that the buffer management here is not ideal,
                // but it's compact enough to fit in an example!
                let len = buffer.len();
                buffer.extend((0..hint).map(|_| 0u8));
                let n = reader.read(&mut buffer[len..])?;
                buffer.truncate(len + n);
                eof = n == 0;
                continue
            }
            Chunk::Parsed { consumed, payload } => {
                let end_section = context.process_payload(payload)?;
                // Cut away the parts from the intermediate buffer that have already been parsed.
                buffer.drain(..consumed);
                if end_section {
                    break
                }
            }
        };
    }
    let finished = context.finish()?;
    Ok(finished)
}

/// Parsing context for the streaming parser in order to capture common shared context.
#[derive(Default)]
pub struct ParseContext {
    /// The Wasm module builder.
    builder: ModuleBuilder,
    /// The Wasm validator and its internal state.
    validator: Validator,
    /// The amount of parsed and validated function bodies.
    count_bodies: u32,
}

impl ParseContext {
    /// Finishes building the Wasm module and returns the Wasm module built so far.
    pub fn finish(self) -> Result<Module, ParseError> {
        self.builder.finish().map_err(Into::into)
    }

    /// Processes the given Wasm payload.
    pub fn process_payload(
        &mut self,
        payload: Payload,
    ) -> Result<bool, ParseError> {
        match payload {
            Payload::Version { num, range } => {
                self.validator.version(num, &range)?;
            }
            Payload::TypeSection(section_reader) => {
                self.parse_type_section(section_reader)?;
            }
            Payload::ImportSection(section_reader) => {
                self.parse_import_section(section_reader)?;
            }
            Payload::FunctionSection(section_reader) => {
                self.parse_function_section(section_reader)?;
            }
            Payload::TableSection(section_reader) => {
                self.parse_table_section(section_reader)?;
            }
            Payload::MemorySection(section_reader) => {
                self.parse_linear_memory_section(section_reader)?;
            }
            Payload::GlobalSection(section_reader) => {
                self.parse_globals_section(section_reader)?;
            }
            Payload::ExportSection(section_reader) => {
                self.parse_export_section(section_reader)?;
            }
            Payload::StartSection { func, range } => {
                self.parse_start_fn(func, range)?;
            }
            Payload::ElementSection(section_reader) => {
                self.parse_element_section(section_reader)?;
            }
            Payload::CodeSectionStart {
                count,
                range,
                size: _,
            } => {
                self.parse_code_section_start(count, range)?;
            }
            Payload::CodeSectionEntry(body) => {
                self.parse_code_section_entry(body)?;
            }
            Payload::DataSection(section_reader) => {
                self.parse_data_section(section_reader)?;
            }

            Payload::DataCountSection { count: _, range: _ } => {
                return Err(SectionError::Unsupported(
                    UnsupportedWasmSection::DataCount,
                ))
                .map_err(Into::into)
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
                return Err(SectionError::Unsupported(
                    UnsupportedWasmSection::Event,
                ))
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
    fn parse_type_section(
        &mut self,
        reader: TypeSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.type_section(&reader)?;
        let count = reader.get_count();
        let mut builder = self.builder.type_section(count)?;
        for type_def in reader {
            match type_def? {
                wasmparser::TypeDef::Func(func_type) => {
                    let fn_sig = func_type.try_into()?;
                    builder.define_type(fn_sig)?;
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
    fn parse_import_section(
        &mut self,
        reader: ImportSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.import_section(&reader)?;
        let count = reader.get_count();
        let mut builder = self.builder.import_section(count)?;
        for import in reader {
            let import = import?;
            let module_name = import.module;
            let field_name = import.field;
            let import_name =
                ImportName::new(module_name, field_name.unwrap_or_default());
            match import.ty {
                ImportSectionEntryType::Function(fn_sig_id) => {
                    builder.import_function(
                        import_name,
                        FunctionSigId::from_u32(fn_sig_id),
                    )?
                }
                ImportSectionEntryType::Table(table_type) => {
                    builder.import_table(
                        import_name,
                        Table::try_from(table_type)?,
                    )?;
                }
                ImportSectionEntryType::Memory(memory_type) => {
                    builder.import_memory(
                        import_name,
                        LinearMemory::try_from(memory_type)?,
                    )?;
                }
                ImportSectionEntryType::Global(global_type) => {
                    builder.import_global(
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

    fn parse_function_section(
        &mut self,
        reader: FunctionSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.function_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.function_section(total_count)?;
        for fn_sig in reader {
            let fn_sig_id = fn_sig?;
            builder.declare_function(FunctionSigId::from_u32(fn_sig_id))?;
        }
        Ok(())
    }

    fn parse_table_section(
        &mut self,
        reader: TableSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.table_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.table_section(total_count)?;
        for table_type in reader {
            let table_type = table_type?;
            builder.declare_table(Table::try_from(table_type)?)?;
        }
        Ok(())
    }

    fn parse_linear_memory_section(
        &mut self,
        reader: MemorySectionReader,
    ) -> Result<(), ParseError> {
        self.validator.memory_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.memory_section(total_count)?;
        for memory_type in reader {
            let memory_type = memory_type?;
            builder.declare_memory(LinearMemory::try_from(memory_type)?)?;
        }
        Ok(())
    }

    fn parse_globals_section(
        &mut self,
        reader: GlobalSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.global_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.global_section(total_count)?;
        for global in reader {
            let global = global?;
            let global_type = GlobalVariable::try_from(global.ty)?;
            let global_init = global.init_expr.try_into()?;
            builder.define_global(global_type, global_init)?;
        }
        Ok(())
    }

    fn parse_export_section(
        &mut self,
        reader: ExportSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.export_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.export_section(total_count)?;
        for export in reader {
            let export = export?;
            let export = Export::try_from(export)?;
            builder.declare_export(export)?;
        }
        Ok(())
    }

    fn parse_start_fn(
        &mut self,
        start_fn_id: u32,
        range: wasmparser::Range,
    ) -> Result<(), ParseError> {
        self.validator.start_section(start_fn_id, &range)?;
        self.builder
            .start_function(FunctionId::from_u32(start_fn_id));
        Ok(())
    }

    fn parse_element_section(
        &mut self,
        reader: ElementSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.element_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.element_section(total_count)?;
        for element in reader {
            let element = element?.try_into()?;
            builder.push_element(element)?;
        }
        Ok(())
    }

    fn parse_code_section_start(
        &mut self,
        count: u32,
        range: wasmparser::Range,
    ) -> Result<(), ParseError> {
        self.validator.code_section_start(count, &range)?;
        let _fn_builder = self.builder.code_section_start(count)?;
        Ok(())
    }

    fn parse_code_section_entry(
        &mut self,
        function_body: wasmparser::FunctionBody,
    ) -> Result<(), ParseError> {
        let mut fn_validator = self.validator.code_section_entry()?;
        let fn_id = FunctionId::from_u32(self.count_bodies);
        let fn_body = FunctionBody::new(fn_id, &mut fn_validator, function_body)?;
        self.builder.code_section_entry(fn_body)?;
        self.count_bodies += 1;
        Ok(())
    }

    fn parse_data_section(
        &mut self,
        reader: DataSectionReader,
    ) -> Result<(), ParseError> {
        self.validator.data_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.data_section(total_count)?;
        for data in reader {
            let data = data?;
            let data = Data::try_from(data)?;
            builder.push_data(data)?;
        }
        Ok(())
    }
}
