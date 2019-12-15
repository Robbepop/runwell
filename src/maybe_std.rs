//! Re-exports an interface that is usable from `std` and `no_std` environments.

use cfg_if::cfg_if;

/// Used to list all re-exported `alloc` crate items from another namespace.
macro_rules! reexport_alloc_from {
    ( $from:ident ) => {
        pub use ::$from::{
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
    }
}

cfg_if! {
    if #[cfg(feature = "std")] {
        // Re-export only `alloc` components from `std`.
        reexport_alloc_from!(std);
    } else {
        // Re-export `alloc` environment.
        reexport_alloc_from!(alloc);
    }
}

/// The prelude shared between `std` and `alloc`.
pub mod prelude {
    pub use super::{
        borrow::ToOwned,
        boxed::Box,
        string::{String, ToString},
        vec::Vec,
        vec,
    };
}
