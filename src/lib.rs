#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

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
mod parser;

pub use parser::{Builder, Escaped, Line, Lines, Parser};
