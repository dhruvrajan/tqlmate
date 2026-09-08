//! Standalone crate for Charon → Aeneas extraction.
//! Re-exports the same pure algorithm as `tqlmate::pure` via path include.

#[path = "../../../src/pure.rs"]
mod pure;

pub use pure::*;
