// We want to translate the Wasm function with ID 89
// into the `runwell` IR that is in SSA form.
// Since function 89 calls functions 120 and 76 we
// also provide their Wasm representations.

// function 89: [i32] => []
// locals
//     2 x i32
// end
// body
//     global.get 0
//     i32.const 16
//     i32sub
//     local.tee 1
//     global.set 0
//     local.get 1
//     i32.const 8
//     i32add
//     local.get 0
//     call 120
//     block
//         local.get 1
//         i32.load offset: 12, alignment: 2
//         local.tee 2
//         eqz
//         brif 0
//         local.get 0
//         i32.load offset: 0, alignment: 2
//         local.get 1
//         i32.load offset: 8, alignment: 2
//         local.get 2
//         call 76
//     end
//     local.get 1
//     i32.const 16
//     i32add
//     global.set 0
// end

// function 120: [i32, i32] => []
// body
//     local.get 0
//     local.get 0
//     i32.load offset: 8, alignment: 2
//     local.get 1
//     call 123
// end

// function 76: [i32, i32] => [i32]
// locals
//     1 x i32
// end
// body
//     local.get 0
//     i32.load offset: 0, alignment: 2
//     local.set 2
//     local.get 0
//     local.get 1
//     i32.store32
//     local.get 2
// end

// The final translated `runwell` IR function:
// It consists of 3 basic blocks.
// Note that this SSA representation is not minimal
// not pruned and not optimized.

// function 89: [%0: i32] => []
//     %1 <- local i32
//     %2 <- local i32
//     %3 <- global.get 0
//     %4 <- i32.const 16
//     %5 <- i32.sub %3 %4
//     local.set 0 <- %5
//     global.set 0 <- %5
//     %6 <- i32.const 8
//     %7 <- i32.add %5 %6
//     %8 <- local.get 0
//     %9 <- call 120 (%7, %8)
//     %10 <- local.get 1
//     %11 <- i32.load 0 offset: 12, alignment: 2
//     local.set 2 <- %11
//     %12 <- local.get 2
//     %13 <- i32.const 0
//     %14 <- i32.cmp -eq %12 %13
//     ite %14 %15 %16
//
// %15 <- block:
//     %17 <- local.get 0
//     %18 <- i32.load 0 offset: 0, alignment: 2
//     %19 <- local.get 1
//     %20 <- i32.load 0 offset: 8, alignment: 2
//     %21 <- local.get 2
//     %22 <- call 76 (%20, %21)
//     br %16
//
// %16 <- block:
//     %23 <- local.get 1
//     %24 <- i32.const 16
//     %25 <- i32.add %23 %24
//     global.set 0 <- %25
//     return
