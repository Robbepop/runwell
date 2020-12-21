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
    BuilderError,
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
    ModuleBuilder,
    ParseError,
    Read,
    ReadError,
    Table,
};
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
    let mut context = <ParseContext<B>>::default();
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
                let end_section = context.process_payload(payload)?;
                // Cut away the parts from the intermediate buffer that have already been parsed.
                buf.drain(..consumed);
                if end_section {
                    break
                }
            }
        };
    }
    let finalized = context.builder.finish().map_err(|_| BuilderError {})?;
    Ok(finalized)
}

/// Parsing context for the streaming parser in order to capture common shared context.
pub struct ParseContext<B> {
    /// The Wasm module builder.
    builder: B,
    /// The Wasm validator and its internal state.
    validator: Validator,
    /// The amount of parsed and validated function bodies.
    count_bodies: u32,
}

impl<B> Default for ParseContext<B>
where
    B: Default,
{
    fn default() -> Self {
        Self {
            builder: B::default(),
            validator: Validator::default(),
            count_bodies: 0,
        }
    }
}

impl<B> ParseContext<B>
where
    B: ModuleBuilder,
{
    fn process_payload(
        &mut self,
        payload: Payload,
    ) -> Result<bool, ParseError> {
        let Self {
            builder,
            validator,
            count_bodies,
        } = self;
        match payload {
            Payload::Version { num, range } => {
                validator.version(num, &range)?;
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
                self.parse_code_start_section(count, range)?;
            }
            Payload::CodeSectionEntry(body) => {
                self.parse_code_section(body)?;
            }
            Payload::DataCountSection { count, range } => {
                self.parse_data_count_section(count, range)?;
            }
            Payload::DataSection(section_reader) => {
                self.parse_data_section(section_reader)?;
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
        let Self {
            builder, validator, ..
        } = self;
        validator.type_section(&reader)?;
        let count = reader.get_count();
        builder.reserve_types(count)?;
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
        let Self {
            builder, validator, ..
        } = self;
        validator.import_section(&reader)?;
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
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.function_section(&reader)?;
        let total_count = reader.get_count();
        builder.reserve_functions(total_count)?;
        for fn_sig in reader {
            let fn_sig_id = fn_sig?;
            builder.declare_function(FunctionSigId::from_u32(fn_sig_id))?;
        }
        Ok(())
    }

    fn parse_table_section(
        &mut self,
        reader: TableSectionReader,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.table_section(&reader)?;
        let total_count = reader.get_count();
        builder.reserve_tables(total_count)?;
        for table_type in reader {
            let table_type = table_type?;
            builder.declare_table(Table::try_from(table_type)?)?;
        }
        Ok(())
    }

    fn parse_linear_memory_section(
        &mut self,
        reader: MemorySectionReader,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.memory_section(&reader)?;
        let total_count = reader.get_count();
        builder.reserve_memories(total_count)?;
        for memory_type in reader {
            let memory_type = memory_type?;
            builder.declare_memory(LinearMemory::try_from(memory_type)?)?;
        }
        Ok(())
    }

    fn parse_globals_section(
        &mut self,
        reader: GlobalSectionReader,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.global_section(&reader)?;
        let total_count = reader.get_count();
        builder.reserve_globals(total_count)?;
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
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.export_section(&reader)?;
        for export in reader {
            let export = export?;
            let export = Export::try_from(export)?;
            builder.declare_export(export);
        }
        Ok(())
    }

    fn parse_start_fn(
        &mut self,
        start_fn_id: u32,
        range: wasmparser::Range,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.start_section(start_fn_id, &range)?;
        builder.set_start_fn(FunctionId::from_u32(start_fn_id));
        Ok(())
    }

    fn parse_element_section(
        &mut self,
        reader: ElementSectionReader,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.element_section(&reader)?;
        let total_count = reader.get_count();
        builder.reserve_elements(total_count)?;
        for element in reader {
            let element = element?.try_into()?;
            builder.define_element(element)?;
        }
        Ok(())
    }

    fn parse_code_start_section(
        &mut self,
        count: u32,
        range: wasmparser::Range,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.code_section_start(count, &range)?;
        builder.reserve_function_bodies(count)?;
        Ok(())
    }

    fn parse_code_section(
        &mut self,
        body: wasmparser::FunctionBody,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder,
            validator,
            count_bodies,
        } = self;
        let mut fn_validator = validator.code_section_entry()?;
        let fn_id = FunctionId::from_u32(*count_bodies);
        let fn_body = FunctionBody::new(fn_id, &mut fn_validator, body)?;
        builder.define_function_body(fn_body)?;
        *count_bodies += 1;
        Ok(())
    }

    fn parse_data_count_section(
        &mut self,
        count: u32,
        range: wasmparser::Range,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.data_count_section(count, &range)?;
        builder.reserve_datas(count)?;
        Ok(())
    }

    fn parse_data_section(
        &mut self,
        reader: DataSectionReader,
    ) -> Result<(), ParseError>
    where
        B: ModuleBuilder,
    {
        let Self {
            builder, validator, ..
        } = self;
        validator.data_section(&reader)?;
        let total_count = reader.get_count();
        builder.reserve_datas(total_count)?;
        for data in reader {
            let data = data?;
            let data = Data::try_from(data)?;
            builder.define_data(data)?;
        }
        Ok(())
    }
}
