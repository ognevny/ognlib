//! # ognlib
//!
//! This is a code that I wrote to practice Rust. There is a big chance that there is some more
//! efficient code already in Crates.io. Nevertheless, with this code I can better learn Rust and
//! features it has.

#![no_std]

pub mod num {
    pub mod methods;
    pub mod power;
    pub mod radix;
}

pub mod algorithm {
    pub mod extra;
    pub mod prime;
    pub mod sort;
}

mod macros;
