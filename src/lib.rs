#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[macro_use]
extern crate log;

#[cfg(not(feature = "std"))]
extern crate alloc;

mod avx;
pub mod index;
mod parser;

pub use parser::{Line, Lines, Parser};
