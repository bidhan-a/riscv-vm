//! # RISC-V Virtual Machine (RV64I)
//!
//! A RISC-V virtual machine implementing the RV64I base integer instruction set.
//!

pub mod memory;
pub mod registers;

// Re-export main types for convenience
pub use memory::Memory;
pub use registers::Registers;
