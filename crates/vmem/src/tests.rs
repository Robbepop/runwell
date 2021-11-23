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

use super::*;

/// Common virtual memory capcities to use in tests.
const TEST_CAPACITIES: &[usize] = &[1, 8, 64, 1024, 4096, 16384, 100_000];

#[test]
fn new_works() {
    fn new_works_for_capacity(capacity: usize) {
        let vmem = VirtualMemory::new(capacity).unwrap();
        assert!(capacity <= vmem.capacity());
    }
    for &capacity in TEST_CAPACITIES {
        new_works_for_capacity(capacity);
    }
}

#[test]
fn new_zero_len_fails() {
    assert!(VirtualMemory::new(0).is_err());
}

#[test]
fn zero_initialization_works() {
    fn zero_initialization_works_for_capacity(capacity: usize) {
        let vmem1 = VirtualMemory::new(capacity).unwrap();
        let vmem2 = VirtualMemory::new(capacity).unwrap();
        // These equalities work since virtually allocated memory
        // is guaranteed to be initialized with zero.
        assert_eq!(&vmem1, &vmem2);
        assert!(vmem1.iter().all(|byte| *byte == 0x00_u8));
        assert!(vmem2.iter().all(|byte| *byte == 0x00_u8));
    }
    for &capacity in TEST_CAPACITIES {
        zero_initialization_works_for_capacity(capacity)
    }
}

#[test]
fn read_write_works() {
    fn read_write_works_for_capacity(capacity: usize) {
        let mut vmem = VirtualMemory::new(capacity).unwrap();
        assert!(capacity <= vmem.capacity());
        let capacity = vmem.capacity();
        for i in 0..capacity {
            vmem[i] = i as u8;
        }
        for i in 0..capacity {
            assert_eq!(vmem[i], i as u8);
        }
    }
    for &capacity in TEST_CAPACITIES {
        read_write_works_for_capacity(capacity)
    }
}

#[test]
fn get_out_of_bounds() {
    fn get_out_of_bounds_for_capacity(capacity: usize) {
        let vmem = VirtualMemory::new(capacity).unwrap();
        let capacity = vmem.capacity();
        assert_eq!(vmem.get(capacity - 1), Some(&0));
        assert_eq!(vmem.get(capacity), None);
    }
    for &capacity in TEST_CAPACITIES {
        get_out_of_bounds_for_capacity(capacity)
    }
}
