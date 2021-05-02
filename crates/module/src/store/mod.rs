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

// mod function;
mod global;
mod memory;
// mod table;
mod trap;
mod value;

use self::{global::GlobalInstance, memory::MemoryInstance};
pub use self::{
    global::{GlobalError, GlobalRef, Mutability},
    memory::{Bytes, MemoryError, MemoryRef, MemoryView, Pages},
    trap::{Trap, TrapCode},
    value::RuntimeValue,
};
use crate::{
    global_var::{Global, GlobalVariableEntity},
    primitive::RunwellPrimitive,
};
use core::cell::RefCell;
use derive_more::{Display, From};
use entity::{ComponentVec, PhantomEntityArena};
use ir::primitive::{LinearMemoryEntity, Mem};

/// Errors that can occur when operating with stores.
#[derive(Debug, Display, From, PartialEq, Eq)]
pub enum StoreError {
    Memory(MemoryError),
    Global(GlobalError),
}

/// The WebAssembly store.
///
/// # Reference
///
/// The store represents all global state that can be manipulated by WebAssembly programs.
/// It consists of the runtime representation of all instances of functions, tables, memories,
/// and globals, element segments, and data segments that have been allocated during the life
/// time of the abstract machine.
#[derive(Debug, Default)]
pub struct Store {
    memories: RefCell<PhantomEntityArena<LinearMemoryEntity>>,
    mem_refs: RefCell<ComponentVec<Mem, MemoryRef>>,
    globals: RefCell<PhantomEntityArena<GlobalVariableEntity>>,
    global_refs: RefCell<ComponentVec<Global, GlobalRef>>,
    // _id_marker: InvariantLifetime<'id>,
}

impl Store {
    /// Allocates a new linear memory to the store and returns a shared reference to it.
    ///
    /// # Note
    ///
    /// The returned linear memory is reference counted.
    pub(super) fn alloc_memory(
        &self,
        minimum_pages: Pages,
        maximum_pages: Option<Pages>,
    ) -> MemoryRef {
        let mem = self.memories.borrow_mut().alloc_some(1);
        let mem_ref = MemoryRef::from_instance(MemoryInstance::new(
            minimum_pages,
            maximum_pages,
        ));
        self.mem_refs.borrow_mut().insert(mem, mem_ref.clone());
        mem_ref
    }

    /// Allocates a new global value to the store and returns a shared reference to it.
    ///
    /// # Note
    ///
    /// The returned global value is reference counted.
    pub(super) fn alloc_global(
        &self,
        initial_value: RuntimeValue,
        mutability: Mutability,
    ) -> GlobalRef {
        let global = self.globals.borrow_mut().alloc_some(1);
        let global_ref = GlobalRef::from_instance(GlobalInstance::new(
            initial_value,
            mutability,
        ));
        self.global_refs
            .borrow_mut()
            .insert(global, global_ref.clone());
        global_ref
    }
}
