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

#[derive(Debug, Clone)]
pub struct OldData {
    pub kind: OldDataKind,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub enum OldDataKind {
    Passive,
    Active {
        memory_index: u32,
        init_expr: OldConstValue,
    },
}

impl<'a> From<wasmparser::Data<'a>> for OldData {
    fn from(data: wasmparser::Data<'a>) -> Self {
        Self {
            kind: OldDataKind::from(data.kind),
            data: data.data.to_vec(),
        }
    }
}

impl<'a> From<wasmparser::DataKind<'a>> for OldDataKind {
    fn from(kind: wasmparser::DataKind<'a>) -> Self {
        match kind {
            wasmparser::DataKind::Passive => Self::Passive,
            wasmparser::DataKind::Active {
                memory_index,
                init_expr,
            } => {
                Self::Active {
                    memory_index,
                    init_expr: interpret_init_expr(init_expr),
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum OldConstValue {
    I32(i32),
    I64(i64),
}

fn interpret_init_expr(_init_expr: wasmparser::InitExpr<'_>) -> OldConstValue {
    OldConstValue::I32(0)
}
