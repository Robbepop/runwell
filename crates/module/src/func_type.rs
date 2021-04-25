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

use crate::primitive::RunwellPrimitive;
use core::{array::IntoIter, fmt};
use ir::primitive::Type;

/// A function type.
#[derive(Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionType {
    /// The amount of inputs.
    len_inputs: usize,
    /// All input types followed by all output types.
    ///
    /// The `len_inputs` field denotes the cut.
    inputs_outputs: Box<[Type]>,
}

impl FunctionType {
    /// Returns a function type builder.
    pub fn build() -> FunctionTypeBuilder {
        FunctionTypeBuilder {
            len_inputs: 0,
            inputs_outputs: Vec::new(),
        }
    }

    /// Returns a slice over all input types.
    pub fn inputs(&self) -> &[Type] {
        &self.inputs_outputs[0..self.len_inputs]
    }

    /// Returns a slice over all output types.
    pub fn outputs(&self) -> &[Type] {
        &self.inputs_outputs[self.len_inputs..]
    }
}

impl fmt::Debug for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FunctionType")
            .field("inputs", &self.inputs())
            .field("outputs", &self.outputs())
            .finish()
    }
}

impl fmt::Display for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Write inputs to formatter.
        match self.inputs().split_first() {
            Some((first, rest)) => {
                if !rest.is_empty() {
                    write!(f, "(")?;
                }
                write!(f, "{}", first)?;
                for input in rest {
                    write!(f, ", {}", input)?;
                }
                if !rest.is_empty() {
                    write!(f, ")")?;
                }
            }
            None => {
                write!(f, "()")?;
            }
        }
        write!(f, " -> ")?;
        // Write outputs to formatter.
        match self.outputs().split_first() {
            Some((first, rest)) => {
                if !rest.is_empty() {
                    write!(f, "(")?;
                }
                write!(f, "{}", first)?;
                for output in rest {
                    write!(f, ", {}", output)?;
                }
                if !rest.is_empty() {
                    write!(f, ")")?;
                }
            }
            None => {
                write!(f, "()")?;
            }
        }
        Ok(())
    }
}

/// Used to incrementally construct function type instances.
#[derive(Debug, PartialEq)]
pub struct FunctionTypeBuilder {
    len_inputs: usize,
    inputs_outputs: Vec<Type>,
}

impl FunctionTypeBuilder {
    /// Returns the number of pushed output types.
    fn len_outputs(&self) -> usize {
        self.inputs_outputs.len() - self.len_inputs
    }

    /// Pushes another input type.
    ///
    /// # Panics
    ///
    /// If output types have already been pushed.
    pub fn push_input<T>(&mut self, input: T)
    where
        T: Into<Type>,
    {
        assert_eq!(
            self.len_outputs(),
            0,
            "cannot push an input type after pushing an output type"
        );
        self.len_inputs += 1;
        self.inputs_outputs.push(input.into());
    }

    /// Pushes another output type.
    ///
    /// # Note
    ///
    /// After pushing an output type you may no longer push input types.
    pub fn push_output<T>(&mut self, output: T)
    where
        T: Into<Type>,
    {
        self.inputs_outputs.push(output.into());
    }

    /// Finalizes the construction of the function type.
    ///
    /// Once a function type has been finalized it can no longer be mutated.
    pub fn finalize(self) -> FunctionType {
        FunctionType {
            len_inputs: self.len_inputs,
            inputs_outputs: self.inputs_outputs.into_boxed_slice(),
        }
    }
}

impl<const I: usize, const O: usize> From<([Type; I], [Type; O])>
    for FunctionType
{
    fn from((inputs, outputs): ([Type; I], [Type; O])) -> Self {
        let mut builder = Self::build();
        for input in IntoIter::new(inputs) {
            builder.push_input(input);
        }
        for output in IntoIter::new(outputs) {
            builder.push_output(output);
        }
        builder.finalize()
    }
}

/// Tuple-types of Runwell primitives implement this trait.
///
/// Those tuple types can be used to statically construct function signatures.
pub trait PrimitiveList: private::Sealed {
    /// Push primitive types to the inputs of a function signature.
    fn push_inputs(builder: &mut FunctionTypeBuilder);
    /// Push primitive types to the output of a function signature.
    fn push_outputs(builder: &mut FunctionTypeBuilder);
}

mod private {
    /// Seals implementers of `PrimitiveList` trait.
    pub trait Sealed {}
}

macro_rules! impl_primitive_list_for {
    ( $( $ty:ident ),* $(,)? ) => {
        #[allow(unused_parens)]
        impl< $($ty),* > self::private::Sealed for ( $($ty),* )
        where
            $(
                $ty: RunwellPrimitive,
            )*
        {}

        #[allow(unused_parens)]
        impl< $($ty),* > PrimitiveList for ( $($ty),* )
        where
            $(
                $ty: RunwellPrimitive,
            )*
        {
            fn push_inputs(__builder: &mut FunctionTypeBuilder) {
                $(
                    __builder.push_input(<$ty as RunwellPrimitive>::TYPE);
                )*
            }

            fn push_outputs(__builder: &mut FunctionTypeBuilder) {
                $(
                    __builder.push_output(<$ty as RunwellPrimitive>::TYPE);
                )*
            }
        }
    };
}
impl_primitive_list_for!();
impl_primitive_list_for!(T0);
impl_primitive_list_for!(T0, T1);
impl_primitive_list_for!(T0, T1, T2);
impl_primitive_list_for!(T0, T1, T2, T3);
impl_primitive_list_for!(T0, T1, T2, T3, T4);
impl_primitive_list_for!(T0, T1, T2, T3, T4, T5);
impl_primitive_list_for!(T0, T1, T2, T3, T4, T5, T6);
impl_primitive_list_for!(T0, T1, T2, T3, T4, T5, T6, T7);
impl_primitive_list_for!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
impl_primitive_list_for!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);

impl FunctionType {
    /// Constructs a function type from the given inputs `I` and output `O` types.
    ///
    /// # Example
    ///
    /// ```
    /// # use ::ir::primitive::{Type, IntType};
    /// # use ::runwell_module::primitive::FunctionType;
    /// let sig = FunctionType::from_types::<(i32, i32), i64>();
    /// assert_eq!(sig.inputs(), &[Type::Int(IntType::I32), Type::Int(IntType::I32)]);
    /// assert_eq!(sig.outputs(), &[Type::Int(IntType::I64)]);
    /// ```
    pub fn from_types<I, O>() -> Self
    where
        I: PrimitiveList,
        O: PrimitiveList,
    {
        let mut builder = Self::build();
        <I as PrimitiveList>::push_inputs(&mut builder);
        <O as PrimitiveList>::push_outputs(&mut builder);
        builder.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ir::primitive::{FloatType, IntType};

    /// Returns the empty function type that takes no inputs and returns no outputs.
    fn empty_func_type() -> FunctionType {
        FunctionType::build().finalize()
    }

    /// Creates a dummy function type for testing.
    fn dummy_func_type() -> FunctionType {
        let mut b = FunctionType::build();
        b.push_input(IntType::I32);
        b.push_input(IntType::I1);
        b.push_input(FloatType::F64);
        b.push_output(IntType::I64);
        b.push_output(FloatType::F32);
        b.finalize()
    }

    #[test]
    fn constructors_works() {
        // Compare with empty function signature. No inputs. No outputs.
        assert_eq!(empty_func_type(), FunctionType::from(([], [])));
        assert_eq!(empty_func_type(), FunctionType::from_types::<(), ()>());
        // Compare with preset dummy function signature.
        assert_eq!(
            dummy_func_type(),
            FunctionType::from((
                [
                    IntType::I32.into(),
                    IntType::I1.into(),
                    FloatType::F64.into()
                ],
                [IntType::I64.into(), FloatType::F32.into()]
            )),
        );
        assert_eq!(
            dummy_func_type(),
            FunctionType::from_types::<(i32, bool, f64), (i64, f32)>(),
        );
    }

    #[test]
    fn inputs_and_outputs_works() {
        use ir::primitive::{FloatType, IntType};

        // Empty Function Type
        let empty_func_type = FunctionType::build().finalize();
        assert_eq!(empty_func_type.inputs(), &[]);
        assert_eq!(empty_func_type.outputs(), &[]);

        // Dummy Function Type
        let dummy_func_type = dummy_func_type();
        assert_eq!(
            dummy_func_type.inputs(),
            &[
                IntType::I32.into(),
                IntType::I1.into(),
                FloatType::F64.into()
            ]
        );
        assert_eq!(
            dummy_func_type.outputs(),
            &[IntType::I64.into(), FloatType::F32.into()]
        );
    }

    #[test]
    fn debug_and_display_works() {
        use ir::primitive::{FloatType, IntType};

        // Empty Function Type
        let empty_func_type = FunctionType::build().finalize();
        assert_eq!(
            format!("{:?}", empty_func_type),
            "FunctionType { inputs: [], outputs: [] }".to_string()
        );
        assert_eq!(format!("{}", empty_func_type), "() -> ()".to_string());

        // Single input and single output
        let single_input_output = {
            let mut builder = FunctionType::build();
            builder.push_input(IntType::I32);
            builder.push_output(FloatType::F32);
            builder.finalize()
        };
        assert_eq!(
            format!("{:?}", single_input_output),
            "FunctionType { inputs: [Int(I32)], outputs: [Float(F32)] }"
                .to_string()
        );
        assert_eq!(
            format!("{}", single_input_output),
            "i32 -> f32".to_string()
        );

        // Dummy Function Type
        let dummy_func_type = dummy_func_type();
        assert_eq!(
            format!("{:?}", dummy_func_type),
            "FunctionType { inputs: [Int(I32), Int(I1), Float(F64)], outputs: [Int(I64), Float(F32)] }"
                .to_string()
        );
        assert_eq!(
            format!("{}", dummy_func_type),
            "(i32, i1, f64) -> (i64, f32)".to_string()
        );
    }
}
