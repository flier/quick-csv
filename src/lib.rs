//! CSV parser which picks up values directly without performing tokenization

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]
#![deny(missing_docs)]

#[macro_use]
extern crate log;
#[macro_use]
extern crate cfg_if;

cfg_if! {
    if #[cfg(feature = "std")] {
        extern crate std as alloc;
    } else {
        extern crate alloc;
    }
}

mod avx;
pub mod index;
pub mod parse;

#[doc(inline)]
pub use index::build;
#[doc(inline)]
pub use parse::parse;
