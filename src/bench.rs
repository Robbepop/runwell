#![cfg(feature = "bench")]

use test::{black_box, Bencher};

use crate::{
    op::{Label, Op},
    vm::{Address, Register, Vm},
};

#[bench]
fn runewell_counter2(b: &mut Bencher) {
    let ops = vec![
        Op::I32Const {
            dst: Register::new(1),
            value: 1,
        },
        Op::I32Const {
            dst: Register::new(2),
            value: 0x80_0000,
        },
        Op::I32Add {
            dst: Register::new(0),
            lhs: Register::new(0),
            rhs: Register::new(1),
        },
        Op::I32Eq {
            dst: Register::new(3),
            lhs: Register::new(0),
            rhs: Register::new(2),
        },
        Op::JumpIf {
            src: Register::new(3),
            to: 2,
        },
    ];
    b.iter(|| Vm::new().execute2(black_box(ops.iter())));
}

#[bench]
fn rust_counter(b: &mut Bencher) {
    b.iter(|| {
        let mut acc = 0;
        while acc < black_box(0x80_0000) {
            acc += 1;
        }
    });
}
