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

use super::{
    Error,
    Export,
    GlobalVariable,
    ImportError,
    ImportName,
    LinearMemoryDecl,
    MemoryDataInit,
    Read,
    TableDecl,
};
use crate::{
    function::translate_function_body,
    table::Element,
    FunctionType,
    InitExpr,
};
use core::convert::TryFrom;
use derive_more::{Display, Error};
use entity::RawIdx;
use ir::primitive::{Func, FuncType};
use module::{Module, ModuleBuilder};
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
    Unexpected(UnexpectedWasmPayload),
    UnsupportedTypeDef(UnsupportedTypeDef),
}

/// An unexpected [`wasmparser::Payload`] has been encountered.
#[derive(Debug, Display, Error, PartialEq, Eq)]
#[display(
    fmt = "encountered unexpected Wasm payload. encountered: {:?}, expected: {:?}",
    encountered,
    expected
)]
pub struct UnexpectedWasmPayload {
    encountered: PayloadKind,
    expected: Option<PayloadKind>,
}

/// The [`wasmparser::Payload`] kind.
#[derive(Debug, PartialEq, Eq)]
pub enum PayloadKind {
    Version,
    TypeSection,
    ImportSection,
    AliasSection,
    InstanceSection,
    FunctionSection,
    TableSection,
    MemorySection,
    EventSection,
    GlobalSection,
    ExportSection,
    StartSection,
    ElementSection,
    DataCountSection,
    DataSection,
    CustomSection,
    CodeSectionStart,
    CodeSectionEntry,
    ModuleSectionStart,
    ModuleSectionEntry,
    UnknownSection,
    End,
}

impl From<Payload<'_>> for PayloadKind {
    fn from(payload: Payload<'_>) -> Self {
        match payload {
            Payload::Version { .. } => Self::Version,
            Payload::TypeSection(_) => Self::TypeSection,
            Payload::ImportSection(_) => Self::ImportSection,
            Payload::AliasSection(_) => Self::AliasSection,
            Payload::InstanceSection(_) => Self::InstanceSection,
            Payload::FunctionSection(_) => Self::FunctionSection,
            Payload::TableSection(_) => Self::TableSection,
            Payload::MemorySection(_) => Self::MemorySection,
            Payload::EventSection(_) => Self::EventSection,
            Payload::GlobalSection(_) => Self::GlobalSection,
            Payload::ExportSection(_) => Self::ExportSection,
            Payload::StartSection { .. } => Self::StartSection,
            Payload::ElementSection(_) => Self::ElementSection,
            Payload::DataCountSection { .. } => Self::DataCountSection,
            Payload::DataSection(_) => Self::DataSection,
            Payload::CustomSection { .. } => Self::CustomSection,
            Payload::CodeSectionStart { .. } => Self::CodeSectionStart,
            Payload::CodeSectionEntry(_) => Self::CodeSectionEntry,
            Payload::ModuleSectionStart { .. } => Self::ModuleSectionStart,
            Payload::ModuleSectionEntry { .. } => Self::ModuleSectionEntry,
            Payload::UnknownSection { .. } => Self::UnknownSection,
            Payload::End { .. } => Self::End,
        }
    }
}

/// Encountered an unsupported binary Wasm section.
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

/// Encountered an unsupported Wasm type definition.
#[derive(Debug, Display, Error, PartialEq, Eq)]
pub enum UnsupportedTypeDef {
    #[display(fmt = "encountered unsupported Wasm type def: instance")]
    Instance,
    #[display(fmt = "encountered unsupported Wasm type def: module")]
    Module,
}

fn pull_more_data<R>(
    hint: u64,
    buffer: &mut Vec<u8>,
    reader: &mut R,
) -> Result<bool, Error>
where
    R: Read,
{
    // Use the hint to preallocate more space, then read
    // some more data into the buffer.
    //
    // Note that the buffer management here is not ideal,
    // but it's compact enough to fit in an example!
    let len = buffer.len();
    buffer.extend((0..hint).map(|_| 0u8));
    let read_bytes = reader.read(&mut buffer[len..])?;
    buffer.truncate(len + read_bytes);
    let eof = read_bytes == 0;
    Ok(eof)
}

/// Parses the binary WebAssembly (Wasm) bytes given through `reader`.
///
/// Returns the fully parsed and validated Wasm module.
///
/// # Note
///
/// Reuses the allocation from the `buffer` bytes vector.
///
/// # Errors
///
/// - If the given Wasm does not validate.
/// - If the given Wasm does not parse properly.
/// - If unsupported Wasm definitions or proposals are encountered.
pub fn parse<R>(mut reader: R, buffer: &mut Vec<u8>) -> Result<Module, Error>
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
                eof = pull_more_data(hint, buffer, &mut reader)?;
                continue
            }
            Chunk::Parsed { consumed, payload } => {
                let end_section = context.process_payload(
                    payload,
                    &mut parser,
                    &mut reader,
                )?;
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
pub struct ParseContext {
    /// The Wasm module builder.
    builder: ModuleBuilder,
    /// The Wasm validator and its internal state.
    validator: Validator,
}

impl Default for ParseContext {
    fn default() -> Self {
        Self {
            builder: Module::build(),
            validator: Default::default(),
        }
    }
}

impl ParseContext {
    /// Finishes building the Wasm module and returns the Wasm module built so far.
    pub fn finish(self) -> Result<Module, Error> {
        self.builder.finalize().map_err(Into::into)
    }

    /// Processes the given Wasm payload.
    pub fn process_payload<R>(
        &mut self,
        payload: Payload,
        parser: &mut Parser,
        reader: &mut R,
    ) -> Result<bool, Error>
    where
        R: Read,
    {
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
                self.parse_memory_section(section_reader)?;
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
                self.parse_code_section(count, range, parser, reader)?;
            }
            Payload::CodeSectionEntry(_body) => {
                return Err(SectionError::Unexpected(UnexpectedWasmPayload {
                    encountered: PayloadKind::CodeSectionEntry,
                    expected: None,
                }))
                .map_err(Into::into)
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
            | Payload::ModuleSectionStart { .. }
            | Payload::ModuleSectionEntry { .. } => {
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
    ) -> Result<(), Error> {
        self.validator.type_section(&reader)?;
        let count = reader.get_count();
        let mut builder = self.builder.type_section()?;
        builder.reserve(count);
        for type_def in reader {
            match type_def? {
                wasmparser::TypeDef::Func(func_type) => {
                    let func_type = FunctionType::try_from(func_type)?;
                    builder.push_type(func_type.into_inner());
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
    ) -> Result<(), Error> {
        self.validator.import_section(&reader)?;
        let _count = reader.get_count();
        let mut builder = self.builder.import_section()?;
        for import in reader {
            let import = import?;
            let module_name = import.module;
            let field_name = import.field;
            let import_name =
                ImportName::new(module_name, field_name.unwrap_or_default());
            match import.ty {
                ImportSectionEntryType::Function(fn_sig_id) => {
                    builder.import_function(
                        import_name.into(),
                        FuncType::from_raw(RawIdx::from_u32(fn_sig_id)),
                    )?;
                }
                ImportSectionEntryType::Table(table_type) => {
                    let table_decl = TableDecl::try_from(table_type)?;
                    builder.import_table(
                        import_name.into(),
                        table_decl.into_inner(),
                    );
                }
                ImportSectionEntryType::Memory(memory_type) => {
                    let memory_decl = LinearMemoryDecl::try_from(memory_type)?;
                    builder.import_memory(
                        import_name.into(),
                        memory_decl.into_inner(),
                    );
                }
                ImportSectionEntryType::Global(global_type) => {
                    let global_decl = GlobalVariable::try_from(global_type)?;
                    builder.import_global(
                        import_name.into(),
                        global_decl.into_inner(),
                    );
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
    ) -> Result<(), Error> {
        self.validator.function_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.function_section()?;
        builder.reserve(total_count);
        for raw_func_type in reader {
            let raw_func_type = raw_func_type?;
            let func_type = FuncType::from_raw(RawIdx::from_u32(raw_func_type));
            builder.push_function(func_type)?;
        }
        Ok(())
    }

    fn parse_table_section(
        &mut self,
        reader: TableSectionReader,
    ) -> Result<(), Error> {
        self.validator.table_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.table_section()?;
        builder.reserve(total_count);
        for table_type in reader {
            let table_type = table_type?;
            let table_decl = TableDecl::try_from(table_type)?;
            builder.push_table(table_decl.into_inner())?;
        }
        Ok(())
    }

    fn parse_memory_section(
        &mut self,
        reader: MemorySectionReader,
    ) -> Result<(), Error> {
        self.validator.memory_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.memory_section()?;
        builder.reserve(total_count);
        for memory_type in reader {
            let memory_type = memory_type?;
            let memory_decl = LinearMemoryDecl::try_from(memory_type)?;
            builder.push_memory(memory_decl.into_inner())?;
        }
        Ok(())
    }

    fn parse_globals_section(
        &mut self,
        reader: GlobalSectionReader,
    ) -> Result<(), Error> {
        self.validator.global_section(&reader)?;
        let total_count = reader.get_count();
        let mut builder = self.builder.global_section()?;
        builder.reserve(total_count);
        for global in reader {
            let global = global?;
            let global_type = GlobalVariable::try_from(global.ty)?;
            let global_init = InitExpr::try_from(global.init_expr)?;
            builder.push_global(
                global_type.into_inner(),
                global_init.into_inner(),
            )?;
        }
        Ok(())
    }

    fn parse_export_section(
        &mut self,
        reader: ExportSectionReader,
    ) -> Result<(), Error> {
        self.validator.export_section(&reader)?;
        let _total_count = reader.get_count();
        let mut builder = self.builder.export_section()?;
        for export in reader {
            let export = export?;
            let export = Export::try_from(export)?;
            let name = export.field();
            match export.item() {
                crate::ExportItem::Function(idx) => {
                    builder.export_function(idx, name)?;
                }
                crate::ExportItem::Table(idx) => {
                    builder.export_table(idx, name)?;
                }
                crate::ExportItem::Memory(idx) => {
                    builder.export_memory(idx, name)?;
                }
                crate::ExportItem::Global(idx) => {
                    builder.export_global(idx, name)?;
                }
            }
        }
        Ok(())
    }

    fn parse_start_fn(
        &mut self,
        start_func: u32,
        range: wasmparser::Range,
    ) -> Result<(), Error> {
        self.validator.start_section(start_func, &range)?;
        self.builder
            .set_start_func(Func::from_raw(RawIdx::from_u32(start_func)))?;
        Ok(())
    }

    fn parse_element_section(
        &mut self,
        reader: ElementSectionReader,
    ) -> Result<(), Error> {
        self.validator.element_section(&reader)?;
        let _total_count = reader.get_count();
        let mut builder = self.builder.table_element_section()?;
        for element in reader {
            let element = Element::try_from(element?)?;
            let table = element.table();
            let func_refs = element.items();
            let offset = element.offset();
            // If any of the element's items was errorneous we stop
            // iteration and raise the errorneous item afterwards.
            // Since this is a lazy operation we need to propagate
            // the potential error after calling `builder.push_element`.
            //
            // In case of multiple errors we only raise the first caught.
            let mut error = None;
            let func_refs = func_refs.into_iter().filter_map(|func_ref| {
                if error.is_some() {
                    return None
                }
                match func_ref {
                    Ok(func_ref) => Some(func_ref),
                    Err(err) => {
                        error = Some(err);
                        None
                    }
                }
            });
            builder.push_element(table, offset, func_refs)?;
            if let Some(error) = error {
                return Err(error)
            }
        }
        Ok(())
    }

    fn parse_code_section<R>(
        &mut self,
        total_count_bodies: u32,
        range: wasmparser::Range,
        parser: &mut Parser,
        reader: &mut R,
    ) -> Result<(), Error>
    where
        R: Read,
    {
        self.validator
            .code_section_start(total_count_bodies, &range)?;
        let (module_view, mut fn_builder) = self.builder.code_section()?;
        fn_builder.reserve(total_count_bodies);
        let mut buffer = <Vec<u8>>::new();
        let mut eof = false;
        let mut count_bodies = 0;
        loop {
            // Parse, validate and feed function body to module builder.
            if count_bodies == total_count_bodies {
                break
            }
            match parser.parse(&buffer, eof)? {
                Chunk::NeedMoreData(hint) => {
                    assert!(!eof); // Otherwise an error would be returned by `parse`.
                    eof = pull_more_data(hint, &mut buffer, reader)?;
                    continue
                }
                Chunk::Parsed {
                    consumed,
                    payload: Payload::CodeSectionEntry(function_body),
                } => {
                    let range = function_body.get_binary_reader().range();
                    let fn_validator = self.validator.code_section_entry()?;
                    let func = Func::from_raw(RawIdx::from_u32(count_bodies));
                    let new_buffer = buffer.drain(consumed..).collect();
                    let fn_buffer = core::mem::replace(&mut buffer, new_buffer);
                    let func_body = translate_function_body(
                        range,
                        fn_buffer,
                        fn_validator,
                        func,
                        module_view,
                    )?;
                    fn_builder.push_body(func, func_body)?;
                    count_bodies += 1;
                    // Cut away the parts from the intermediate buffer that have already been parsed.
                    // buffer.drain(..consumed); // <- Not required since we are currently swapping out the buffer.
                }
                Chunk::Parsed {
                    consumed,
                    payload: Payload::CustomSection { .. },
                } => {
                    // Ignore all custom sections and drain buffer accordingly.
                    buffer.drain(..consumed);
                }
                Chunk::Parsed {
                    consumed: _,
                    payload,
                } => {
                    return Err(SectionError::Unexpected(
                        UnexpectedWasmPayload {
                            encountered: payload.into(),
                            expected: Some(PayloadKind::CodeSectionEntry),
                        },
                    ))
                    .map_err(Into::into)
                }
            };
        }
        Ok(())
    }

    fn parse_data_section(
        &mut self,
        reader: DataSectionReader,
    ) -> Result<(), Error> {
        self.validator.data_section(&reader)?;
        let _total_count = reader.get_count();
        let mut builder = self.builder.memory_data_section()?;
        for data in reader {
            let data = data?;
            let data = MemoryDataInit::try_from(data)?;
            let memory = data.memory();
            let bytes = data.bytes();
            let offset = data.offset().into_inner();
            builder.push_data(memory, offset, bytes.iter().copied())?;
        }
        Ok(())
    }
}
