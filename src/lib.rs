//! # ognlib
//!
//! This is a code that I wrote to practice Rust. There is a big chance that there is some more
//! efficient code already in Crates.io. Nevertheless, with this code I can better learn Rust and
//! features it has.

#![allow(clippy::modulo_arithmetic)]
#![allow(clippy::arithmetic_side_effects)]
#![allow(clippy::missing_inline_in_public_items)]
#![allow(clippy::implicit_return)]
#![allow(clippy::default_numeric_fallback)]
#![allow(clippy::std_instead_of_core)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::question_mark_used)]
#![allow(clippy::integer_division)]

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
