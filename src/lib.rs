#![allow(unused)]
#![cfg_attr(feature = "bench", feature(test))]

#[cfg(feature = "bench")]
extern crate test;

mod op;
// mod parser;
pub mod ir;
pub mod parse;
mod vm;

mod bench;

// Function 184 of type FuncType { form: Func, params: [I32, I32, I32], returns: [I32] }
//     I32Const { value: 0 }
//     LocalSet { local_index: 3 }
//     Block { ty: Type(EmptyBlockType) }
//         LocalGet { local_index: 2 }
//         I32Eqz
//         BrIf { relative_depth: 0 }
//         Block { ty: Type(EmptyBlockType) }
//             Loop { ty: Type(EmptyBlockType) }
//                 LocalGet { local_index: 0 }
//                 I32Load8U { memarg: MemoryImmediate { flags: 0, offset: 0 } }
//                 LocalTee { local_index: 4 }
//                 LocalGet { local_index: 1 }
//                 I32Load8U { memarg: MemoryImmediate { flags: 0, offset: 0 } }
//                 LocalTee { local_index: 5 }
//                 I32Ne
//                 BrIf { relative_depth: 1 }
//                 LocalGet { local_index: 1 }
//                 I32Const { value: 1 }
//                 I32Add
//                 LocalSet { local_index: 1 }
//                 LocalGet { local_index: 0 }
//                 I32Const { value: 1 }
//                 I32Add
//                 LocalSet { local_index: 0 }
//                 LocalGet { local_index: 2 }
//                 I32Const { value: -1 }
//                 I32Add
//                 LocalTee { local_index: 2 }
//                 I32Eqz
//                 BrIf { relative_depth: 2 }
//                 Br { relative_depth: 0 }
//             End
//         End
//         LocalGet { local_index: 4 }
//         LocalGet { local_index: 5 }
//         I32Sub
//         LocalSet { local_index: 3 }
//     End
//     LocalGet { local_index: 3 }
// End

// Function 184 of type FuncType { form: Func, params: [I32, I32, I32], returns: [I32] }
//     %v3 = alloca i32
//     %v4 = alloca i32
//     %v5 = alloca i32
//     store %v2 <- 0
//     br %f184b0

// f184b0:
//     %v6 = %v2
//     %v7 = icmp -eq %v6 0
//     ite %v7 then: %f184b1 else: %f184b2

// f184b1:
//     %v8 = %v0
//     %v9 = load i8, from %v8, memory: { flags: 0, offset: 0 }
//     %v10 = zext i32 %v9
//     store %v4 <- %v10
//     %v11 = %v1
//     %v12 = load i8, from %v11, memory: { flags: 0, offset: 0 }
//     %v13 = zext i32 %v12
//     store %v5 <- %13
//     %v14 = icmp -ne %v4 %v5
//     ite %v14 then: %f184b2 else: %f184b3

// f184b2:
//     %v15 = %v4
//     %v16 = %v5
//     %v17 = isub %v16 %v15
//     store %3 %v17
//     br %f184b4

// f184b3:
//     %v19 = %v1
//     %v20 = iadd %v19 1
//     store %v1 %v20
//     %v21 = %v0
//     %v22 = iadd %v21 1
//     store %v0 %v22
//     %v23 = %v2
//     %v24 = iadd %v23 -1
//     store %v2 <- %v24
//     %v25 = icmp -eq %v24 0
//     ite %v25 then: %f184b4 else: %f184b3

// f184b4:
//     %v18 = %v3
//     return %v18
