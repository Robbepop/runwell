// Copyright 2019 Robin Freyler
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

//! Structures and routines for parsing and validating WebAssembly (Wasm).
//!
//! Use the [`Module::new`] constructor in order to parse and validate
//! a Wasm encoded stream of bytes.

use crate::maybe_std::prelude::*;
use core::convert::TryFrom;
use derive_more::{Display, From};
use thiserror::Error;
use wasmparser::{
    CodeSectionReader,
    Export,
    ExportSectionReader,
    FuncType,
    FunctionBody,
    FunctionSectionReader,
    GlobalSectionReader,
    Import,
    ImportSectionEntryType,
    ImportSectionReader,
    MemorySectionReader,
    MemoryType,
    ModuleReader,
    Operator,
    SectionCode,
    Type,
    TypeSectionReader,
};

/// An index into the type table of a Wasm module.
#[derive(Debug, Copy, Clone)]
pub struct TypeId(usize);

impl TypeId {
    /// Returns the underlying type ID.
    pub fn get(self) -> usize {
        self.0
    }
}

/// An index into the internal function table of a Wasm module.
#[derive(Debug, Copy, Clone)]
pub struct InternalFunctionId(usize);

impl InternalFunctionId {
    /// Returns the `FunctionId` for `self`.
    pub fn into_function_id(self, module: &Module) -> FunctionId {
        FunctionId(self.get() + module.len_imported_fns())
    }

    /// Returns the underlying ID.
    pub fn get(self) -> usize {
        self.0
    }
}

/// An index into the function table of a Wasm module.
#[derive(Debug, Copy, Clone)]
pub struct FunctionId(usize);

impl FunctionId {
    /// Returns the internal function ID of `self`
    /// or `None` if `self` refers to an imported function.
    pub fn into_internal_function_id(
        self,
        module: &Module,
    ) -> Option<InternalFunctionId> {
        let id = self.get();
        let imported_fns = module.len_imported_fns();
        if id < imported_fns {
            return None
        }
        Some(InternalFunctionId(id - imported_fns))
    }

    /// Returns the underlying ID.
    pub fn get(self) -> usize {
        self.0
    }
}

/// A function declaration.
#[derive(Debug, From)]
pub struct FunctionDeclaration {
    /// The underlying function type.
    fn_type: wasmparser::FuncType,
}

impl FunctionDeclaration {
    /// Returns a slice over the input types of `self`.
    pub fn inputs(&self) -> &[Type] {
        &self.fn_type.params
    }

    /// Returns a slice over the output types of `self`.
    pub fn outputs(&self) -> &[Type] {
        &self.fn_type.returns
    }
}

/// A parsed and validated WebAssembly (Wasm) module.
#[derive(Debug)]
pub struct Module<'a> {
    /// Types accessible through the Wasm type table.
    ///
    /// Mainly the types of functions are stored here.
    types: Vec<FunctionDeclaration>,
    /// Imported function declarations from the Wasm module.
    imported_fns: Vec<TypeId>,
    /// Imported global variable declarations from the Wasm module.
    imported_globals: Vec<GlobalVariableDecl>,
    /// Indices into the `types` table for every function in order.
    fn_decls: Vec<TypeId>,
    /// The linear memory section and its limits.
    memory: MemoryType,
    /// Global variable definitions.
    globals: Vec<GlobalVariableDef<'a>>,
    /// Export definitions.
    exports: Vec<Export<'a>>,
    /// Function bodies for every function in order.
    ///
    /// # Note
    ///
    /// A function body consists of the local variables and
    /// all the operations within the function.
    fn_defs: Vec<FunctionDefinition<'a>>,
    /// Optional start function.
    ///
    /// # Note
    ///
    /// If this is `Some` the Wasm module is an executable,
    /// otherwise it is a library.
    start_fn: Option<FunctionId>,
}

impl<'a> Module<'a> {
    /// Constructs a Wasm module from the raw parts.
    ///
    /// # Errors
    ///
    /// If the raw parts do not combine to valid Wasm.
    fn from_raw_parts(
        types: Vec<FunctionDeclaration>,
        imported_fns: Vec<TypeId>,
        imported_globals: Vec<GlobalVariableDecl>,
        fn_decls: Vec<TypeId>,
        memory: MemoryType,
        globals: Vec<GlobalVariableDef<'a>>,
        exports: Vec<Export<'a>>,
        fn_defs: Vec<FunctionDefinition<'a>>,
        start_fn: Option<FunctionId>,
    ) -> Result<Self, ParseError> {
        if fn_decls.len() != fn_defs.len() {
            return Err(ParseError::UnmatchingFnDeclToDef)
        }
        Ok(Self {
            types,
            imported_fns,
            imported_globals,
            fn_decls,
            memory,
            globals,
            exports,
            fn_defs,
            start_fn,
        })
    }

    /// Returns the linear memory declaation.
    ///
    /// # Note
    ///
    /// Currently only one linear memory entry is allowed.
    pub fn memory(&self) -> &MemoryType {
        &self.memory
    }

    /// Returns the identified type from the type table.
    pub fn get_type(&self, id: TypeId) -> &FunctionDeclaration {
        &self.types[id.get()]
    }

    /// Returns the declaration of the identified function.
    pub fn get_fn_decl(&self, id: FunctionId) -> &FunctionDeclaration {
        self.get_type(self.fn_decls[id.get()])
    }

    /// Returns the definition of the identified function.
    pub fn get_fn_def(&self, id: InternalFunctionId) -> &FunctionDefinition {
        &self.fn_defs[id.get()]
    }

    /// Returns the function at index `id`.
    pub fn get_fn(&self, id: InternalFunctionId) -> Function {
        let decl = self.get_fn_decl(id.into_function_id(self));
        let def = self.get_fn_def(id);
        Function { id, decl, def }
    }

    /// Returns the start function, if any.
    pub fn start_fn(&self) -> Option<FunctionId> {
        self.start_fn
    }

    /// Returns an iterator over the function declarations and definitions.
    pub fn iter_fns(&self) -> FunctionIter {
        FunctionIter {
            module: self,
            current: 0,
        }
    }

    /// Returns an iterator over the function declarations and definitions.
    ///
    /// # Note
    ///
    /// This excludes imported functions.
    pub fn iter_imported_fns(&self) -> ImportedFunctionIter {
        ImportedFunctionIter::new(self)
    }

    /// Returns an iterator over the global variable definitions.
    ///
    /// # Note
    ///
    /// This excludes imported global variables.
    pub fn iter_globals(&self) -> core::slice::Iter<GlobalVariableDef<'a>> {
        self.globals.iter()
    }

    /// Returns an iterator over the imported global variable declarations.
    pub fn iter_imported_globals(
        &self,
    ) -> core::slice::Iter<GlobalVariableDecl> {
        self.imported_globals.iter()
    }

    /// Returns an iterator over the exported items.
    pub fn iter_exports(&self) -> core::slice::Iter<Export<'a>> {
        self.exports.iter()
    }

    /// Returns the number of functions in the Wasm module.
    fn len_fns(&self) -> usize {
        debug_assert_eq!(self.fn_decls.len(), self.fn_defs.len());
        self.fn_decls.len()
    }

    /// Returns the number of imported function in the Wasm module.
    fn len_imported_fns(&self) -> usize {
        self.imported_fns.len()
    }

    /// Returns the number of global variable definitions in the Wasm module.
    fn len_globals(&self) -> usize {
        self.globals.len()
    }

    /// Returns the number of imported global variables in the Wasm module.
    fn len_imported_globals(&self) -> usize {
        self.imported_fns.len()
    }
}

/// An iterator over the functions of a Wasm module.
#[derive(Debug)]
pub struct FunctionIter<'a> {
    /// The iterated Wasm module.
    module: &'a Module<'a>,
    /// The current function index of the iteration.
    current: usize,
}

impl<'a> Iterator for FunctionIter<'a> {
    type Item = Function<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == self.module.len_fns() {
            return None
        }
        let id = InternalFunctionId(self.current);
        let decl = self.module.get_fn_decl(id.into_function_id(&self.module));
        let def = self.module.get_fn_def(id);
        let fun = Self::Item { id, decl, def };
        self.current += 1;
        Some(fun)
    }
}

/// A Wasm function.
#[derive(Debug)]
pub struct Function<'a> {
    /// The global unique identifier of the function.
    id: InternalFunctionId,
    /// The function declaration.
    decl: &'a FunctionDeclaration,
    /// The function definition.
    def: &'a FunctionDefinition<'a>,
}

impl Function<'_> {
    /// The global unique function identifier.
    pub fn id(&self) -> InternalFunctionId {
        self.id
    }

    /// The input types of the function.
    pub fn inputs(&self) -> &[Type] {
        self.decl.inputs()
    }

    /// The output types of the function.
    pub fn outputs(&self) -> &[Type] {
        self.decl.outputs()
    }

    /// The local variable declarations of the function.
    pub fn locals(&self) -> &[(usize, Type)] {
        self.def.locals()
    }

    /// The operations executed by the function.
    pub fn ops(&self) -> &[Operator] {
        self.def.ops()
    }
}

pub struct ImportedFunctionIter<'a> {
    /// The iterated Wasm module.
    module: &'a Module<'a>,
    /// The iterated over imported function type IDs.
    ids: core::iter::Enumerate<core::slice::Iter<'a, TypeId>>,
}

impl<'a> ImportedFunctionIter<'a> {
    pub fn new(module: &'a Module) -> Self {
        Self {
            module,
            ids: module.imported_fns.iter().enumerate(),
        }
    }
}

impl<'a> Iterator for ImportedFunctionIter<'a> {
    type Item = ImportedFunction<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.ids.next()
            .map(|(id, &type_id)| {
                let id = FunctionId(id);
                let decl = self.module.get_type(type_id);
                Self::Item { id, decl }
            })
    }
}

/// A Wasm function.
#[derive(Debug)]
pub struct ImportedFunction<'a> {
    /// The global unique identifier of the function.
    id: FunctionId,
    /// The function declaration.
    decl: &'a FunctionDeclaration,
}

impl ImportedFunction<'_> {
    /// The global unique function identifier.
    pub fn id(&self) -> FunctionId {
        self.id
    }

    /// The input types of the function.
    pub fn inputs(&self) -> &[Type] {
        self.decl.inputs()
    }

    /// The output types of the function.
    pub fn outputs(&self) -> &[Type] {
        self.decl.outputs()
    }
}

/// A function definition.
#[derive(Debug)]
pub struct FunctionDefinition<'b> {
    /// The locals of the function.
    locals: Vec<(usize, Type)>,
    /// The operations of the function.
    ops: Vec<Operator<'b>>,
}

impl FunctionDefinition<'_> {
    /// Returns a slice over the local variable declarations.
    pub fn locals(&self) -> &[(usize, Type)] {
        &self.locals
    }

    /// Returns a non-empty slice over the Wasm operations of the function.
    pub fn ops(&self) -> &[Operator] {
        &self.ops
    }
}

/// A global variable declaration.
#[derive(Debug)]
pub struct GlobalVariableDecl {
    /// The type of the global variable.
    ty: Type,
    /// If the global variable is mutable.
    is_mutable: bool,
}

impl GlobalVariableDecl {
    /// Returns the type of the global variable.
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    /// Returns `true` if the global variable is mutable.
    pub fn is_mutable(&self) -> bool {
        self.is_mutable
    }
}

/// A global variable definition of a Wasm module.
#[derive(Debug)]
pub struct GlobalVariableDef<'a> {
    /// The global variable declaration.
    decl: GlobalVariableDecl,
    /// The initialization procedure of the global variable.
    initializer: Vec<Operator<'a>>,
}

impl GlobalVariableDef<'_> {
    /// Returns the declaration of the global variable.
    pub fn decl(&self) -> &GlobalVariableDecl {
        &self.decl
    }

    /// Returns the operations executed by the
    /// global variable's initialization procedure.
    pub fn initializer(&self) -> &[Operator] {
        &self.initializer
    }
}

/// An error that can be encountered upon parsing a Wasm module.
#[derive(Debug, Display, From)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum ParseError {
    /// An error encountered in the underlying parser.
    #[display(fmt = "encountered parser error")]
    Parser(wasmparser::BinaryReaderError),
    /// Encountered upon unmatching function declarations and definitions.
    #[display(fmt = "unmatching fn declarations and definitions")]
    #[from(ignore)]
    UnmatchingFnDeclToDef,
    /// Encountered upon encountering multiple memory section entries.
    #[display(fmt = "multiple memory entries are unsupported, yet")]
    #[from(ignore)]
    MultipleMemoriesUnsupported,
    /// Missing a linear memory section or entry.
    #[display(fmt = "missing linear memory section or entry")]
    #[from(ignore)]
    MissingMemoryEntry,
    /// Min-max linear memory section does not match.
    #[display(fmt = "unmatching minimum and maximum linear memory limits")]
    #[from(ignore)]
    UnmatchingMinMaxMemoryLimits,
}

impl<'b> Module<'b> {
    /// Parses a byte stream representing a binary Wasm module.
    ///
    /// # Dev Note
    ///
    /// - For the sake of simplicity we ignore custom sections.
    /// - We have to skip custom section after every step
    ///   since they might appear out of order.
    /// - The binary Wasm sections are guaranteed to be in the following order.
    ///   Sections are optional and may be missing.
    ///
    /// | Section  | Description                              |
    /// |----------|------------------------------------------|
    /// | Type     | Function signature declarations |
    /// | Import   | Import declarations |
    /// | Function | Function declarations |
    /// | Table    | Indirect function table and other tables |
    /// | Memory   | Memory attributes |
    /// | Global   | Global declarations |
    /// | Export   | Exports |
    /// | Start    | Start function declaration |
    /// | Element  | Elements section |
    /// | Code     | Function bodies (code) |
    /// | Data     | Data segments |
    pub fn new(bytes: &'b [u8]) -> Result<Self, ParseError> {
        let mut types = Vec::new();
        let mut imported_fns = Vec::new();
        let mut imported_globals = Vec::new();
        let mut fn_decls = Vec::new();
        let mut globals = Vec::new();
        let mut exports = Vec::new();
        let mut fn_defs = Vec::new();
        let mut memory = None;
        let mut start_fn = None;
        let mut reader = ModuleReader::new(bytes)?;
        loop {
            reader.skip_custom_sections()?;
            if reader.eof() {
                break
            }
            let section = reader.read()?;
            match section.code {
                SectionCode::Type => {
                    Self::extract_types(
                        &mut types,
                        section.get_type_section_reader()?,
                    )
                }
                SectionCode::Import => {
                    Self::extract_imports(
                        &mut imported_fns,
                        &mut imported_globals,
                        &mut memory,
                        section.get_import_section_reader()?,
                    )
                }
                SectionCode::Function => {
                    Self::extract_fn_types(
                        &mut fn_decls,
                        section.get_function_section_reader()?,
                    )
                }
                SectionCode::Table => Ok(()),
                SectionCode::Memory => {
                    Self::extract_memories(
                        &mut memory,
                        section.get_memory_section_reader()?,
                    )
                }
                SectionCode::Global => {
                    Self::extract_globals(
                        &mut globals,
                        section.get_global_section_reader()?,
                    )
                }
                SectionCode::Export => {
                    Self::extract_exports(
                        &mut exports,
                        section.get_export_section_reader()?,
                    )
                }
                SectionCode::Start => {
                    Self::extract_start_fn(
                        &mut start_fn,
                        section.get_start_section_content()?,
                    )
                }
                SectionCode::Element => Ok(()),
                SectionCode::Code => {
                    Self::extract_code(
                        &mut fn_defs,
                        section.get_code_section_reader()?,
                    )
                }
                SectionCode::Data => Ok(()),
                SectionCode::DataCount => Ok(()),
                _ => unreachable!("encountered unsupported custom section"),
            }?
        }
        let memory = memory.ok_or_else(|| ParseError::MissingMemoryEntry)?;
        Self::from_raw_parts(
            types,
            imported_fns,
            imported_globals,
            fn_decls,
            memory,
            globals,
            exports,
            fn_defs,
            start_fn,
        )
    }

    /// Extracts the types from the `type` section and
    /// converts them into `runwell` Wasm entities.
    fn extract_types(
        types: &mut Vec<FunctionDeclaration>,
        mut section: TypeSectionReader,
    ) -> Result<(), ParseError> {
        debug_assert!(types.is_empty());
        for func_type in section.into_iter() {
            types.push(FunctionDeclaration::from(func_type?));
        }
        Ok(())
    }

    /// Extracts the import declarations from the `import` section.
    fn extract_imports<'a>(
        imported_fns: &mut Vec<TypeId>,
        imported_globals: &mut Vec<GlobalVariableDecl>,
        memory: &mut Option<MemoryType>,
        mut section: ImportSectionReader<'a>,
    ) -> Result<(), ParseError> {
        debug_assert!(imported_fns.is_empty());
        debug_assert!(imported_globals.is_empty());
        for import in section.into_iter() {
            let import = import?;
            match import.ty {
                ImportSectionEntryType::Memory(ty) => {
                    Self::validate_and_update_memory(ty, memory)?
                }
                ImportSectionEntryType::Function(function) => {
                    imported_fns.push(TypeId(function as usize))
                }
                ImportSectionEntryType::Global(global) => {
                    imported_globals.push(GlobalVariableDecl {
                        ty: global.content_type,
                        is_mutable: global.mutable,
                    })
                }
                ImportSectionEntryType::Table(_) => {}
            }
        }
        Ok(())
    }

    /// Extracts the declarations from the `function` section and
    /// converts them into `runwell` Wasm entities.
    fn extract_fn_types(
        fn_types: &mut Vec<TypeId>,
        mut section: FunctionSectionReader,
    ) -> Result<(), ParseError> {
        debug_assert!(fn_types.is_empty());
        *fn_types = section
            .into_iter()
            .map(|id| Ok(TypeId(id? as usize)))
            .collect::<Result<_, ParseError>>()?;
        Ok(())
    }

    /// Extracts the linear memory declarations from the `memory` section.
    fn extract_memories(
        memory: &mut Option<MemoryType>,
        mut section: MemorySectionReader,
    ) -> Result<(), ParseError> {
        let memories = section.into_iter().collect::<Result<Vec<_>, _>>()?;
        if memories.is_empty() {
            return Err(ParseError::MissingMemoryEntry)
        }
        if memories.len() >= 2 {
            return Err(ParseError::MultipleMemoriesUnsupported)
        }
        Self::validate_and_update_memory(memories[0], memory)
    }

    /// Validates the parsed memory type and properly updates it for the module.
    fn validate_and_update_memory(
        wasm_memory: MemoryType,
        rw_memory: &mut Option<MemoryType>,
    ) -> Result<(), ParseError> {
        if rw_memory.is_some() {
            return Err(ParseError::MultipleMemoriesUnsupported)
        }
        // TODO: Un-uncomment these lines to re-enable the check.
        // if Some(wasm_memory.limits.initial) != wasm_memory.limits.maximum {
        //     return Err(ParseError::UnmatchingMinMaxMemoryLimits)
        // }
        *rw_memory = Some(wasm_memory);
        Ok(())
    }

    /// Extracts the definitions from the `global` section and
    /// converts them into `runwell` Wasm entities.
    fn extract_globals<'a>(
        globals: &mut Vec<GlobalVariableDef<'a>>,
        mut section: GlobalSectionReader<'a>,
    ) -> Result<(), ParseError> {
        debug_assert!(globals.is_empty());
        *globals = section
            .into_iter()
            .map(|global| {
                let global = global?;
                let ty = global.ty.content_type;
                let is_mutable = global.ty.mutable;
                let initializer = global
                    .init_expr
                    .get_operators_reader()
                    .into_iter()
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(GlobalVariableDef {
                    decl: GlobalVariableDecl { ty, is_mutable },
                    initializer,
                })
            })
            .collect::<Result<Vec<_>, ParseError>>()?;
        Ok(())
    }

    /// Extracts the export definitions from the `export` section.
    fn extract_exports<'a>(
        exports: &mut Vec<Export<'a>>,
        mut section: ExportSectionReader<'a>,
    ) -> Result<(), ParseError> {
        debug_assert!(exports.is_empty());
        for export in section.into_iter() {
            exports.push(export?);
        }
        Ok(())
    }

    /// Extracts the starting function.
    fn extract_start_fn(
        start_fn: &mut Option<FunctionId>,
        content: u32,
    ) -> Result<(), ParseError> {
        *start_fn = Some(FunctionId(content as usize));
        Ok(())
    }

    /// Extracts the definitions from the `code` section and
    /// converts them into `runwell` Wasm entities.
    fn extract_code<'a>(
        fn_bodies: &mut Vec<FunctionDefinition<'a>>,
        mut section: CodeSectionReader<'a>,
    ) -> Result<(), ParseError> {
        debug_assert!(fn_bodies.is_empty());
        *fn_bodies = section
            .into_iter()
            .map(|fn_body| {
                let fn_body = fn_body?;
                Ok(FunctionDefinition {
                    locals: fn_body
                        .get_locals_reader()?
                        .into_iter()
                        .map(|local| {
                            let local = local?;
                            Ok((local.0 as usize, local.1))
                        })
                        .collect::<Result<_, ParseError>>()?,
                    ops: fn_body
                        .get_operators_reader()?
                        .into_iter()
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, ParseError>>()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_incrementer() {
        let wasm = include_bytes!("../incrementer.wasm");
        let module = Module::new(wasm).expect("couldn't parse Wasm module");
        for fun in module.iter_imported_fns().take(2) {
            println!("\n\n{:#?}", fun);
        }
        for fun in module.iter_fns().take(2) {
            println!("\n\n{:#?}", fun);
        }
        for global_variable in module.iter_globals().take(2) {
            println!("\n{:#?}", global_variable)
        }
        for export in module.iter_exports().take(2) {
            println!("\n{:#?}", export);
        }
        println!("\nmemory = {:#?}", module.memory);
        println!("\nstart fn           = {:#?}", module.start_fn());
        println!("# imported fns     = {:#?}", module.len_imported_fns());
        println!("# fns              = {:#?}", module.len_fns());
        println!("# imported globals = {:#?}", module.len_imported_globals());
        println!("# globals          = {:#?}", module.len_globals());
    }
}
