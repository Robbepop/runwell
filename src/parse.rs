//! Structures and routines for parsing and validating WebAssembly (Wasm).

use core::convert::TryFrom;
use derive_more::From;
use std::io::Read;
use thiserror::Error;
use wasmparser::{
    CodeSectionReader,
    FuncType,
    FunctionBody,
    FunctionSectionReader,
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

/// An index into the function table of a Wasm module.
#[derive(Debug, Copy, Clone)]
pub struct FunctionId(usize);

impl FunctionId {
    /// Returns the underlying function ID.
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
    /// Indices into the `types` table for every function in order.
    fn_decls: Vec<TypeId>,
    /// Function bodies for every function in order.
    ///
    /// # Note
    ///
    /// A function body consists of the local variables and
    /// all the operations within the function.
    fn_defs: Vec<FunctionDefinition<'a>>,
}

impl<'a> Module<'a> {
    /// Constructs a Wasm module from the raw parts.
    ///
    /// # Errors
    ///
    /// If the raw parts do not combine to valid Wasm.
    fn from_raw_parts(
        types: Vec<FunctionDeclaration>,
        fn_decls: Vec<TypeId>,
        fn_defs: Vec<FunctionDefinition<'a>>,
    ) -> Result<Self, ModuleError> {
        if fn_decls.len() != fn_defs.len() {
            return Err(ModuleError::UnmatchingFnDeclToDef)
        }
        Ok(Self {
            types,
            fn_decls,
            fn_defs,
        })
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
    pub fn get_fn_def(&self, id: FunctionId) -> &FunctionDefinition {
        &self.fn_defs[id.get()]
    }

    /// Returns an iterator over the function declarations and definitions.
    pub fn iter_fns(&self) -> FunctionIter {
        FunctionIter {
            module: self,
            current: 0,
        }
    }

    /// Returns the number of functions in the Wasm module.
    fn len_fns(&self) -> usize {
        debug_assert_eq!(self.fn_decls.len(), self.fn_defs.len());
        self.fn_decls.len()
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

/// A Wasm function.
#[derive(Debug)]
pub struct Function<'a> {
    /// The global unique identifier of the function.
    id: FunctionId,
    /// The function declaration.
    decl: &'a FunctionDeclaration,
    /// The function definition.
    def: &'a FunctionDefinition<'a>,
}

impl Function<'_> {
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

    /// The local variable declarations of the function.
    pub fn locals(&self) -> &[(usize, Type)] {
        self.def.locals()
    }

    /// The operations executed by the function.
    pub fn ops(&self) -> &[Operator] {
        self.def.ops()
    }
}

impl<'a> Iterator for FunctionIter<'a> {
    type Item = Function<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == self.module.len_fns() {
            return None
        }
        let id = FunctionId(self.current);
        let decl = self.module.get_fn_decl(id);
        let def = self.module.get_fn_def(id);
        let fun = Self::Item { id, decl, def };
        self.current += 1;
        Some(fun)
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

/// An error that can be encountered upon parsing a Wasm module.
#[derive(Debug, Error)]
pub enum ModuleError {
    /// An error encountered in the underlying parser.
    #[error("encountered parser error")]
    Parser(#[from] wasmparser::BinaryReaderError),
    /// Encountered upon unmatching function declarations and definitions.
    #[error("unmatching fn declarations and definitions")]
    UnmatchingFnDeclToDef,
}

impl<'b> Module<'b> {
    /// Parses a byte stream representing a binary Wasm module.
    ///
    /// # Dev Note
    ///
    /// - For the sake of simplicity we ignore custom section such as the `name` section.
    /// - We have to skip custom section after every step since they might appear out of order.
    /// - The binary Wasm sections are guaranteed to be in the following order.
    ///   Some sections may be missing.
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
    pub fn new(bytes: &'b [u8]) -> Result<Self, ModuleError> {
        let mut types = Vec::new();
        let mut fn_decls = Vec::new();
        let mut fn_defs = Vec::new();
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
                SectionCode::Import => Ok(()),
                SectionCode::Function => {
                    Self::extract_fn_types(
                        &mut fn_decls,
                        section.get_function_section_reader()?,
                    )
                }
                SectionCode::Table => Ok(()),
                SectionCode::Memory => Ok(()),
                SectionCode::Global => Ok(()),
                SectionCode::Export => Ok(()),
                SectionCode::Start => Ok(()),
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
        Self::from_raw_parts(types, fn_decls, fn_defs)
    }

    /// Extracts the types from the `type` section and converts them into `runwell` entities.
    fn extract_types(
        types: &mut Vec<FunctionDeclaration>,
        mut section: TypeSectionReader,
    ) -> Result<(), ModuleError> {
        *types = section
            .into_iter()
            .map(|func_type| Ok(FunctionDeclaration::from(func_type?)))
            .collect::<Result<_, ModuleError>>()?;
        Ok(())
    }

    /// Extracts the declarations from the `function` section and converts them into `runwell` entities.
    fn extract_fn_types(
        fn_types: &mut Vec<TypeId>,
        mut section: FunctionSectionReader,
    ) -> Result<(), ModuleError> {
        *fn_types = section
            .into_iter()
            .map(|id| Ok(TypeId(id? as usize)))
            .collect::<Result<_, ModuleError>>()?;
        Ok(())
    }

    /// Extracts the definitions from the `code` section and converts them into `runwell` entities.
    fn extract_code<'a>(
        fn_bodies: &mut Vec<FunctionDefinition<'a>>,
        mut section: CodeSectionReader<'a>,
    ) -> Result<(), ModuleError> {
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
                        .collect::<Result<_, ModuleError>>()?,
                    ops: fn_body
                        .get_operators_reader()?
                        .into_iter()
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, ModuleError>>()?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_incrementer() {
        let wasm = std::fs::read("incrementer.wasm")
            .expect("couldn't read `incrementer.wasm`");
        let module = Module::new(&wasm).expect("couldn't parse Wasm module");
        // println!("module = {:#?}", module);
        for fun in module.iter_fns().take(3) {
            println!("\n\n{:#?}", fun);
        }
    }
}
