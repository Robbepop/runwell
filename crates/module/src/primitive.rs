// Copyright 2021 Robin Freyler
//
// Licensed under the Apache License, Version 2.0 (the "Licen offset: (), len: (), pages: () offset: (), len: (), pages: ()se");
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

use ir::primitive::{FloatType, IntType, Type};
pub use super::{
    func_body::{Instr, Variable},
    func_type::FunctionType,
    global_var::{Global, GlobalVariable, GlobalVariableEntity},
    import_name::ImportName,
    init_expr::InitExpr,
    linear_memory::{DataSegmentIter, LinearMemoryDecl, LinearMemoryInit},
    table::{ElementSegmentIter, TableDecl, TableInit},
};

/// Implemented by all WebAssembly primitives.
///
/// Used to serialization and deserialization from and into bytes.
pub trait RunwellPrimitive: Default + Sized {
    /// The byte representation of the Wasm primitive.
    type ByteRepr: AsRef<[u8]> + AsMut<[u8]>;

    /// The Runwell type of the primitive type.
    const TYPE: Type;

    /// Converts the Wasm primitive into its bytes representation.
    fn into_bytes(self) -> Self::ByteRepr;

    /// Creates the Wasm primitive from the given bytes.
    fn from_bytes(bytes: Self::ByteRepr) -> Self;
}

macro_rules! impl_wasm_primitive {
    ( $( ($prim:ty, $rw_ty:expr) ),* $(,)? ) => {
        $(
            impl RunwellPrimitive for $prim {
                type ByteRepr = [::core::primitive::u8; ::core::mem::size_of::<$prim>()];
                const TYPE: Type = $rw_ty;

                #[inline]
                fn into_bytes(self) -> Self::ByteRepr {
                    self.to_le_bytes()
                }

                #[inline]
                fn from_bytes(bytes: Self::ByteRepr) -> Self {
                    Self::from_le_bytes(bytes)
                }
            }
        )*
    };
}
impl_wasm_primitive! {
    (u8, Type::Int(IntType::I8)),
    (i8, Type::Int(IntType::I8)),
    (u16, Type::Int(IntType::I16)),
    (i16, Type::Int(IntType::I16)),
    (u32, Type::Int(IntType::I32)),
    (i32, Type::Int(IntType::I32)),
    (u64, Type::Int(IntType::I64)),
    (i64, Type::Int(IntType::I64)),
    (f32, Type::Float(FloatType::F32)),
    (f64, Type::Float(FloatType::F64)),
}

impl RunwellPrimitive for bool {
    type ByteRepr = [u8; core::mem::size_of::<bool>()];
    const TYPE: Type = Type::Int(IntType::I1);

    #[inline]
    fn into_bytes(self) -> Self::ByteRepr {
        [self as u8]
    }

    #[inline]
    fn from_bytes(bytes: Self::ByteRepr) -> Self {
        bytes[0] != 0
    }
}
