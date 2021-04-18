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

use core::fmt;
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
        write!(f, "[")?;
        if let Some((first, rest)) = self.inputs().split_first() {
            write!(f, "{}", first)?;
            for input in rest {
                write!(f, ", {}", input)?;
            }
        }
        write!(f, "] => [")?;
        if let Some((first, rest)) = self.outputs().split_first() {
            write!(f, "{}", first)?;
            for output in rest {
                write!(f, ", {}", output)?;
            }
        }
        write!(f, "]")?;
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Creates a dummy function type for testing.
    fn dummy_func_type() -> FunctionType {
        use ir::primitive::{FloatType, IntType};
        let mut b = FunctionType::build();
        b.push_input(IntType::I32);
        b.push_input(IntType::I1);
        b.push_input(FloatType::F64);
        b.push_output(IntType::I64);
        b.push_output(FloatType::F32);
        b.finalize()
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
        // Empty Function Type
        let empty_func_type = FunctionType::build().finalize();
        assert_eq!(
            format!("{:?}", empty_func_type),
            "FunctionType { inputs: [], outputs: [] }".to_string()
        );
        assert_eq!(format!("{}", empty_func_type), "[] => []".to_string());

        // Dummy Function Type
        let dummy_func_type = dummy_func_type();
        assert_eq!(
            format!("{:?}", dummy_func_type),
            "FunctionType { inputs: [Int(I32), Int(I1), Float(F64)], outputs: [Int(I64), Float(F32)] }"
                .to_string()
        );
        assert_eq!(
            format!("{}", dummy_func_type),
            "[i32, i1, f64] => [i64, f32]".to_string()
        );
    }
}
