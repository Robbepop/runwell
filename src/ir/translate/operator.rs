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

use crate::{
    ir::{
        operator::{int::*, *},
        translate::FunctionTranslator,
        Binding,
    },
    parse,
    parse::{LocalVariableId, Type},
};

/// Implemented by `runwell` IR operators to translate from Wasm.
pub trait TranslateOperator {
    /// Translate the operator from Wasm to `runwell` IR on a function level.
    fn translate_operator(&self, translator: &mut FunctionTranslator);
}

impl parse::Operator {
    fn translate_drop_op(&self, translator: &mut FunctionTranslator) {
        translator.stack.pop();
    }

    fn translate_select_op(&self, translator: &mut FunctionTranslator) {
        let (cond_val, cond_ty) = translator.stack_pop();
        let (then_val, then_ty) = translator.stack_pop();
        let (else_val, else_ty) = translator.stack_pop();
        assert_eq!(cond_ty, Type::I32);
        assert_eq!(then_ty, else_ty);
        translator.push_op(
            SelectOp::new(cond_val, then_ty, then_val, else_val),
            else_ty, // Avoid clone: `then_ty` == `else_ty` at this point
        );
    }

    fn translate_return_op(&self, translator: &mut FunctionTranslator) {
        let (ret, ty) = translator.stack_pop();
        translator.push_unbinded_op(TerminalOp::from(ReturnOp::new(ty, ret)));
    }

    fn translate_unreachable_op(&self, translator: &mut FunctionTranslator) {
        translator.push_unbinded_op(TerminalOp::Unreachable);
    }
}

impl TranslateOperator for parse::Operator {
    fn translate_operator(&self, translator: &mut FunctionTranslator) {
        match self {
            Self::Nop => {}
            Self::Unreachable => self.translate_unreachable_op(translator),
            Self::Block(op) => op.translate_operator(translator),
            Self::Const(op) => op.translate_operator(translator),
            Self::Drop => self.translate_drop_op(translator),
            Self::Select => self.translate_select_op(translator),
            Self::Return => self.translate_return_op(translator),
            Self::LocalGet(op) => op.translate_operator(translator),
            Self::LocalSet(op) => op.translate_operator(translator),
            Self::LocalTee(op) => op.translate_operator(translator),
            Self::GlobalGet(op) => op.translate_operator(translator),
            Self::GlobalSet(op) => op.translate_operator(translator),
            Self::Add(op) => op.translate_operator(translator),
            Self::End => {}
            _ => todo!(),
        }
    }
}

impl TranslateOperator for parse::operator::GlobalGetOp {
    fn translate_operator(&self, _translator: &mut FunctionTranslator) {
        todo!()
    }
}

impl TranslateOperator for parse::operator::GlobalSetOp {
    fn translate_operator(&self, _translator: &mut FunctionTranslator) {
        todo!()
    }
}

impl TranslateOperator for parse::operator::LocalGetOp {
    fn translate_operator(&self, translator: &mut FunctionTranslator) {
        let entry = translator.get_local_binding(self.id).clone();
        // translator.stack_push(entry.binding, entry.ty);
        translator.push_op(
            LoadOp::load_local(entry.ty.clone(), entry.binding),
            entry.ty,
        );
    }
}

impl TranslateOperator for parse::operator::AddOp {
    fn translate_operator(&self, translator: &mut FunctionTranslator) {
        let (rhs, rhs_ty) = translator.stack_pop();
        let (lhs, lhs_ty) = translator.stack_pop();
        assert_eq!(rhs_ty, lhs_ty);
        translator.push_op(IntOp::from(AddOp::new(lhs_ty, lhs, rhs)), rhs_ty);
    }
}

/// Pushes a local variable store operation to the current block
/// of the translator.
fn push_store_local(
    translator: &mut FunctionTranslator,
    dst_id: LocalVariableId,
    src_binding: Binding,
    src_ty: Type,
) {
    let dst = translator.get_local_binding(dst_id).clone();
    assert_eq!(dst.ty, src_ty);
    translator.push_unbinded_op(StoreOp::store_local(
        dst.ty,
        dst.binding,
        src_binding,
    ));
}

impl TranslateOperator for parse::operator::LocalSetOp {
    fn translate_operator(&self, translator: &mut FunctionTranslator) {
        let (popped_bind, popped_ty) = translator.stack_pop();
        push_store_local(translator, self.id, popped_bind, popped_ty);
    }
}

impl TranslateOperator for parse::operator::LocalTeeOp {
    fn translate_operator(&self, translator: &mut FunctionTranslator) {
        let (popped_bind, popped_ty) = translator.stack_last().clone();
        push_store_local(translator, self.id, popped_bind, popped_ty);
    }
}

impl TranslateOperator for parse::operator::BlockOp {
    fn translate_operator(&self, _translator: &mut FunctionTranslator) {
        todo!()
    }
}

impl TranslateOperator for parse::operator::ConstOp {
    fn translate_operator(&self, translator: &mut FunctionTranslator) {
        match self {
            Self::I32(val) => {
                translator.push_op(ConstOp::from(*val), Type::I32);
            }
            Self::I64(val) => {
                translator.push_op(ConstOp::from(*val), Type::I64);
            }
        }
    }
}
