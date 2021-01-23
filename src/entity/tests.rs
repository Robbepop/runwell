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

//! Unit tests for the secondary data structures that store the components.
//!
//! The unit tests for the primary data structures is kept in the `primary`
//! submodule directly. Tests for the secondary data structures are kept in
//! their parent module since they require the primary data structures in
//! order to properly be used.

use super::{ComponentMap, ComponentVec};
use crate::entity::{Idx, RawIdx};

#[derive(Debug)]
pub enum TestEntity {}

fn u32_to_idx(raw_value: u32) -> Idx<TestEntity> {
    Idx::from_raw(RawIdx::from_u32(raw_value))
}

macro_rules! unit_test_secondary {
    ( $name:ident ) => {
        #[test]
        fn default_works() {
            let default = $name::default();
            let null = super::u32_to_idx(0);

            assert!(default.is_empty());
            assert_eq!(default.len(), 0);
            assert!(!default.contains_key(null));
            assert_eq!(default.get(null), None);
            assert_eq!(default.iter().count(), 0);
            let mut default = default;
            assert_eq!(default.get_mut(null), None);
            assert_eq!(default.iter_mut().count(), 0);
        }

        /// Returns a populated instance from the given iterator.
        fn populated_instance<I>(init_values: I) -> $name
        where
            I: IntoIterator<Item = (u32, char)>,
        {
            let mut instance = $name::default();
            let mut expected_len = 0;
            // Asserts that none of the init values is already contained
            // and inserts all values and assert that they are contained
            // after the insertion.
            for (k, c) in init_values {
                let k = super::u32_to_idx(k);

                assert!(!instance.contains_key(k));
                assert_eq!(instance.get(k), None);
                assert_eq!(instance.insert(k, c), None);
                assert!(instance.contains_key(k));
                assert_eq!(instance.get(k), Some(&c));
                expected_len += 1;
                assert_eq!(instance.len(), expected_len);
            }
            instance
        }

        /// Returns a sample set of inputs for testing.
        fn some_components_with_holes() -> Vec<(u32, char)> {
            vec![(0, 'A'), (1, 'B'), (3, 'D'), (10, 'E')]
        }

        /// Returns a scrambled insert pattern.
        fn scambled_inserts() -> Vec<(u32, char)> {
            vec![(0, 'A'), (3, 'D'), (1, 'B'), (2, 'C')]
        }

        #[test]
        fn insert_works() {
            // Single component.
            populated_instance(vec![(0, 'A')]);
            // Two consecutive components.
            populated_instance(vec![(0, 'A'), (1, 'B')]);
            // Some components with holes.
            populated_instance(some_components_with_holes());
            // Scrambled input pattern.
            populated_instance(scambled_inserts());
        }

        #[test]
        fn remove_works() {
            let sample = some_components_with_holes();
            let mut instance = populated_instance(sample.clone());
            let mut expected_len = sample.len();
            // Asserts that all of the populated values are already contained
            // and remove all populated value and assert that they are no longer
            // contained after the removal.
            for (k, c) in sample {
                let k = super::u32_to_idx(k);

                assert!(instance.contains_key(k));
                assert_eq!(instance.get(k), Some(&c));
                assert_eq!(instance.remove(k), Some(c));
                assert!(!instance.contains_key(k));
                assert_eq!(instance.get(k), None);
                expected_len -= 1;
                assert_eq!(instance.len(), expected_len);
            }
            assert!(instance.is_empty());
        }

        #[test]
        fn iter_works() {
            let sample = some_components_with_holes();
            let instance = populated_instance(sample.clone());

            // Asserts that iterating over the secondary data structure
            // yields the correct elements. The order in which the components
            // are yielded does not matter.
            let expected = sample
                .iter()
                .map(|(k, c)| (super::u32_to_idx(*k), c))
                .collect::<Vec<_>>();
            let mut actual = instance.iter().collect::<Vec<_>>();
            actual.sort();
            assert_eq!(actual, expected);
        }

        #[test]
        fn clear_works() {
            let sample = some_components_with_holes();
            let mut instance = populated_instance(sample.clone());
            instance.clear();
            // Asserts that the secondary data structure no longer
            // contains any of the sample keys, is empty and does not
            // yield components upon iteration.
            for &(k, _) in &sample {
                let k = super::u32_to_idx(k);

                assert!(!instance.contains_key(k));
            }
            assert!(instance.is_empty());
            assert_eq!(instance.len(), 0);
            assert_eq!(instance.iter().count(), 0);
        }

        #[test]
        fn clone_works() {
            // Assert clone of empty is still empty.
            let empty = $name::default();
            let clone1 = empty.clone();
            assert_eq!(empty, clone1);
            // Assert clone of populated is equal.
            let sample = some_components_with_holes();
            let instance = populated_instance(sample.clone());
            let clone2 = instance.clone();
            assert_eq!(instance, clone2);
        }

        #[test]
        fn partial_eq_works() {
            let sample1 = vec![(0, 'A'), (2, 'C'), (4, 'E')];
            let sample2 = vec![(1, 'B'), (3, 'D'), (5, 'F')];

            // 4 instances with 2 different samples.
            let instance1 = populated_instance(sample1.clone());
            let instance2 = populated_instance(sample2.clone());
            let instance3 = populated_instance(sample1);
            let instance4 = populated_instance(sample2);

            // Assert that `==` for equal samples.
            assert_eq!(instance1, instance3);
            assert_eq!(instance2, instance4);

            // Assert that `!=` for inequal samples.
            assert_ne!(instance1, instance2);
            assert_ne!(instance3, instance4);
        }
    };
}

mod map {
    use super::{ComponentMap, TestEntity};
    use crate::entity::Idx;

    type TestComponentMap = ComponentMap<Idx<TestEntity>, char>;
    unit_test_secondary!(TestComponentMap);
}

mod vec {
    use super::{ComponentVec, TestEntity};
    use crate::entity::Idx;

    type TestComponentVec = ComponentVec<Idx<TestEntity>, char>;
    unit_test_secondary!(TestComponentVec);
}
