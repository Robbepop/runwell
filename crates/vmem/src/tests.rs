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

/// Common virtual memory buffer lengths to use in tests.
const TEST_LENS: &[usize] = &[1, 8, 64, 1024, 4096, 16384, 100_000];

#[test]
fn new_works() {
    fn new_works_for_len(len: usize) {
        let vmem = VirtualMemory::new(len).unwrap();
        assert_eq!(vmem.len(), len);
        assert!(vmem.len() <= vmem.capacity());
    }
    for &len in TEST_LENS {
        new_works_for_len(len);
    }
}

#[test]
fn grow_to_capacity_works() {
    let mut vmem = VirtualMemory::new(1).unwrap();
    let capacity_before = vmem.capacity();
    // Grow the virtually allocated memory to its current capacity.
    vmem.grow(vmem.capacity() - vmem.len()).unwrap();
    let capacity_after = vmem.capacity();
    // Make sure that the capacity stayed the same and length
    // is now equal to the capacity.
    assert_eq!(capacity_before, capacity_after);
    assert_eq!(vmem.len(), vmem.capacity());
}

#[test]
fn grow_works() {
    let mut vmem = VirtualMemory::new(1).unwrap();
    let capacity_before = vmem.capacity();
    // Grow length by its current capacity
    // so that a virtual memory resize operation
    // has to be performed.
    vmem.grow(vmem.capacity()).unwrap();
    let capacity_after = vmem.capacity();
    assert_ne!(capacity_before, capacity_after);
}

#[test]
fn new_zero_len_fails() {
    assert!(VirtualMemory::new(0).is_err());
}

#[test]
fn zero_initialization_works() {
    fn zero_initialization_works_for_len(len: usize) {
        let vmem1 = VirtualMemory::new(len).unwrap();
        let vmem2 = VirtualMemory::new(len).unwrap();
        // These equalities work since virtually allocated memory
        // is guaranteed to be initialized with zero.
        assert_eq!(vmem1, vmem2);
        assert!(vmem1.iter().all(|byte| *byte == 0x00_u8));
        assert!(vmem2.iter().all(|byte| *byte == 0x00_u8));
    }
    for &len in TEST_LENS {
        zero_initialization_works_for_len(len)
    }
}

#[test]
fn read_write_works() {
    fn read_write_works_for_len(len: usize) {
        let mut vmem = VirtualMemory::new(len).unwrap();
        assert_eq!(vmem.len(), len);
        for i in 0..len {
            vmem[i] = i as u8;
        }
        for i in 0..len {
            assert_eq!(vmem[i], i as u8);
        }
    }
    for &len in TEST_LENS {
        read_write_works_for_len(len)
    }
}

#[test]
fn get_byte_out_of_bounds() {
    fn get_byte_out_of_bounds_for_len(len: usize) {
        let vmem = VirtualMemory::new(len).unwrap();
        assert_eq!(vmem.get(len - 1), Some(&0));
        assert_eq!(vmem.get(len), None);
    }
    for &len in TEST_LENS {
        get_byte_out_of_bounds_for_len(len)
    }
}
