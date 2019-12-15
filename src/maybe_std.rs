//! Re-exports an interface that is usable from `std` and `no_std` environments.

use cfg_if::cfg_if;

cfg_if! {
    if #[cfg(feature = "std")] {
        // Re-export only `alloc` components from `std`.
        pub use std::{
            alloc,
            borrow,
            boxed,
            collections,
            fmt,
            rc,
            slice,
            str,
            string,
            sync,
            vec,
            format,
        };
    } else {
        // Re-export `alloc` environment.
        pub use ::alloc::*;
    }
}

pub mod prelude {
    pub use super::{
        borrow::ToOwned,
        boxed::Box,
        string::{String, ToString},
        vec::Vec,
        vec,
    };
}
