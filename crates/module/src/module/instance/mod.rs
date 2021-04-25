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

mod store;

pub use self::store::{
    Bytes,
    GlobalError,
    GlobalRef,
    MemoryError,
    MemoryRef,
    MemoryView,
    Mutability,
    Pages,
    RuntimeValue,
    Store,
    StoreError,
    Trap,
    TrapCode,
};

// use crate::Module;
// use self::{
//     memory::{MemoryInstance, Pages},
//     table::TableInstance,
// };
// use core::cell::RefCell;
// use entity::ComponentMap;
// use ir::primitive::{Mem, Table};

// #[derive(Debug)]
// pub struct ModuleInstance {
//     memories: RefCell<ComponentMap<Mem, MemoryInstance>>,
//     tables: RefCell<ComponentMap<Table, TableInstance>>,
// }

// impl ModuleInstance {
//     /// Creates a new instance from the given module.
//     pub fn new(module: &Module, resolver: ImportsResolver) -> Self {
//         Self {
//             memories: Self::instantiate_memories(module),
//             tables: Self::instantiate_tables(module),
//         }
//     }

//     // /// Evaluates the given initializer expression to a constant for indexing.
//     // fn evaluate_init_expr_offset(init_expr: &InitExpr) -> u32 {
//     //     match init_expr {
//     //         InitExpr::Const(const_value) => {
//     //             match const_value {
//     //                 ir::primitive::Const::Int(int_const) => {
//     //                     let offset = int_const.into_bits64();
//     //                     assert!(offset <= u32::MAX as u64);
//     //                     offset as u32
//     //                 }
//     //                 ir::primitive::Const::Bool(_)
//     //                 | ir::primitive::Const::Float(_)
//     //                 | ir::primitive::Const::Ptr(_) => {
//     //                     panic!("encountered invalid initializer expression for offset")
//     //                 }
//     //             }
//     //         }
//     //         InitExpr::GlobalGet(_) => {
//     //             unimplemented!("cannot yet look-up global variable values");
//     //         }
//     //     }
//     // }

//     // /// Instantiates linear memories for the module.
//     // fn instantiate_memories(
//     //     module: &'a Module,
//     // ) -> ComponentMap<Mem, LinearMemoryContents> {
//     //     let mut memories = ComponentMap::default();
//     //     for (mem, init) in &module.res.memory_inits {
//     //         let mut contents = LinearMemoryContents::default();
//     //         for (offset, bytes) in init {
//     //             let offset = Self::evaluate_init_expr_offset(offset);
//     //             contents.initialize(offset, bytes);
//     //         }
//     //         memories.insert(mem, contents);
//     //     }
//     //     memories
//     // }

//     // /// Instantiates tables for the module.
//     // fn instantiate_tables(
//     //     module: &'a Module,
//     // ) -> ComponentMap<Table, TableContents> {
//     //     let mut tables = ComponentMap::default();
//     //     for (table, init) in &module.res.table_inits {
//     //         let mut contents = TableContents::default();
//     //         for (offset, funcs) in init {
//     //             let offset = Self::evaluate_init_expr_offset(offset);
//     //             contents.initialize(offset, funcs);
//     //         }
//     //         tables.insert(table, contents);
//     //     }
//     //     tables
//     // }
// }
