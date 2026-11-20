#![forbid(unsafe_code)]

pub mod approx;
pub mod check;
pub mod codec;
pub mod decimal;
pub mod eval;
pub mod float;
pub mod ir;
pub mod math;
pub mod nat;
pub mod print;
pub mod read;
pub mod runtime;

#[cfg(kani)]
mod proofs;
