//! # RISC-V Virtual Machine (RV64I)
//!
//! A RISC-V virtual machine implementing the RV64I base integer instruction set.
//!

pub mod cpu;
pub mod memory;
pub mod registers;

pub use cpu::{CPU, PrivilegeMode};
pub use memory::Memory;
pub use registers::Registers;
