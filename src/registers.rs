//! # RISC-V Register File
//!
//! ## Overview
//! The RISC-V architecture defines 32 general-purpose integer registers (x0-x31),
//! each 64 bits wide in RV64I. Register x0 is hardwired to the constant 0.
//!
//!
//! | Register | ABI Name | Description                    | Saved by |
//! |----------|----------|--------------------------------|----------|
//! | x0       | zero     | Hard-wired zero                | -        |
//! | x1       | ra       | Return address                 | Caller   |
//! | x2       | sp       | Stack pointer                  | Callee   |
//! | x3       | gp       | Global pointer                 | -        |
//! | x4       | tp       | Thread pointer                 | -        |
//! | x5-x7    | t0-t2    | Temporary registers            | Caller   |
//! | x8       | s0/fp    | Saved register/Frame pointer   | Callee   |
//! | x9       | s1       | Saved register                 | Callee   |
//! | x10-x11  | a0-a1    | Function args/return values    | Caller   |
//! | x12-x17  | a2-a7    | Function arguments             | Caller   |
//! | x18-x27  | s2-s11   | Saved registers                | Callee   |
//! | x28-x31  | t3-t6    | Temporary registers            | Caller   |
//!

/// Register file containing 32 general-purpose 64-bit registers
///
/// # RISC-V ISA Requirement
/// Register x0 is hardwired to constant 0. Any writes to x0 are discarded,
/// and reads from x0 always return 0.
///
/// # Memory Layout
/// Registers are stored in a fixed-size array for O(1) access time.
#[derive(Debug, Clone)]
pub struct Registers {
    /// Internal storage for 32 registers (x0-x31)
    /// Note: x0 is included in the array but writes to it are ignored
    regs: [u64; 32],
}

impl Registers {
    /// Creates a new register file with all registers initialized to 0
    ///
    /// # Examples
    /// ```
    /// use riscv_vm::registers::Registers;
    ///
    /// let regs = Registers::new();
    /// assert_eq!(regs.read(0), 0);  // x0 is always 0
    /// assert_eq!(regs.read(1), 0);  // Other registers start at 0
    /// ```
    pub fn new() -> Self {
        Self { regs: [0; 32] }
    }

    /// Reads the value from a register
    ///
    /// # Arguments
    /// * `reg` - Register number (0-31)
    ///
    /// # Returns
    /// The 64-bit value stored in the register. For x0, always returns 0.
    ///
    /// # Panics
    /// Panics if `reg` >= 32 (invalid register number)
    ///
    ///
    /// # Examples
    /// ```
    /// use riscv_vm::registers::Registers;
    ///
    /// let mut regs = Registers::new();
    /// regs.write(5, 42);
    /// assert_eq!(regs.read(5), 42);
    /// assert_eq!(regs.read(0), 0);  // x0 always 0
    /// ```
    #[inline]
    pub fn read(&self, reg: u8) -> u64 {
        assert!(reg < 32, "Invalid register number: {}", reg);

        // x0 is hardwired to 0, even if the internal array has a different value
        if reg == 0 { 0 } else { self.regs[reg as usize] }
    }

    /// Writes a value to a register
    ///
    /// # Arguments
    /// * `reg` - Register number (0-31)
    /// * `value` - 64-bit value to write
    ///
    /// # Panics
    /// Panics if `reg` >= 32
    ///
    /// # Examples
    /// ```
    /// use riscv_vm::registers::Registers;
    ///
    /// let mut regs = Registers::new();
    /// regs.write(1, 100);
    /// assert_eq!(regs.read(1), 100);
    ///
    /// // Writing to x0 is a no-op
    /// regs.write(0, 999);
    /// assert_eq!(regs.read(0), 0);
    /// ```
    #[inline]
    pub fn write(&mut self, reg: u8, value: u64) {
        assert!(reg < 32, "Invalid register number: {}", reg);

        // Writes to x0 are discarded (x0 is hardwired to 0)
        if reg != 0 {
            self.regs[reg as usize] = value;
        }
    }

    /// Resets all registers to 0
    ///
    /// Useful for initializing the CPU state or resetting the state between test runs.
    ///
    /// # Examples
    /// ```
    /// use riscv_vm::registers::Registers;
    ///
    /// let mut regs = Registers::new();
    /// regs.write(5, 42);
    /// regs.reset();
    /// assert_eq!(regs.read(5), 0);
    /// ```
    pub fn reset(&mut self) {
        self.regs = [0; 32];
    }

    /// Returns a slice of all register values for debugging purposes
    pub fn dump(&self) -> &[u64; 32] {
        &self.regs
    }
}

impl Default for Registers {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_registers_all_zero() {
        let regs = Registers::new();
        for i in 0..32 {
            assert_eq!(
                regs.read(i),
                0,
                "Register x{} should be initialized to 0",
                i
            );
        }
    }

    #[test]
    fn test_x0_always_zero() {
        let regs = Registers::new();
        assert_eq!(regs.read(0), 0, "x0 must be 0 initially");
    }

    #[test]
    fn test_x0_write_ignored() {
        let mut regs = Registers::new();

        // Try to write various values to x0
        regs.write(0, 42);
        assert_eq!(regs.read(0), 0, "x0 must remain 0 after write");

        regs.write(0, u64::MAX);
        assert_eq!(regs.read(0), 0, "x0 must remain 0 even with MAX value");

        regs.write(0, 0xDEADBEEF);
        assert_eq!(regs.read(0), 0, "x0 must remain 0 with any value");
    }

    #[test]
    fn test_read_write_normal_register() {
        let mut regs = Registers::new();

        // Test writing and reading to x1
        regs.write(1, 42);
        assert_eq!(regs.read(1), 42, "x1 should store the written value");

        // Test overwriting
        regs.write(1, 100);
        assert_eq!(regs.read(1), 100, "x1 should update with new value");
    }

    #[test]
    fn test_all_registers_independent() {
        let mut regs = Registers::new();

        // Write unique values to all non-zero registers
        for i in 1..32 {
            regs.write(i, i as u64 * 100);
        }

        // Verify each register has its unique value
        for i in 1..32 {
            assert_eq!(
                regs.read(i),
                i as u64 * 100,
                "Register x{} should maintain its value independently",
                i
            );
        }

        // x0 should still be 0
        assert_eq!(regs.read(0), 0, "x0 must remain 0");
    }

    #[test]
    fn test_boundary_values() {
        let mut regs = Registers::new();

        // Test with 0
        regs.write(5, 0);
        assert_eq!(regs.read(5), 0);

        // Test with u64::MAX
        regs.write(5, u64::MAX);
        assert_eq!(regs.read(5), u64::MAX);

        // Test with mid-range value
        regs.write(5, 0x8000_0000_0000_0000);
        assert_eq!(regs.read(5), 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_reset() {
        let mut regs = Registers::new();

        // Write values to several registers
        regs.write(1, 10);
        regs.write(5, 50);
        regs.write(31, 310);

        // Reset all registers
        regs.reset();

        // All registers should be 0
        for i in 0..32 {
            assert_eq!(regs.read(i), 0, "Register x{} should be 0 after reset", i);
        }
    }

    #[test]
    #[should_panic(expected = "Invalid register number")]
    fn test_read_invalid_register() {
        let regs = Registers::new();
        let _ = regs.read(32); // Should panic
    }

    #[test]
    #[should_panic(expected = "Invalid register number")]
    fn test_write_invalid_register() {
        let mut regs = Registers::new();
        regs.write(33, 42); // Should panic
    }

    #[test]
    fn test_dump() {
        let mut regs = Registers::new();
        regs.write(1, 10);
        regs.write(2, 20);

        let dump = regs.dump();
        assert_eq!(dump.len(), 32);
        assert_eq!(dump[0], 0); // x0 is always 0
        assert_eq!(dump[1], 10);
        assert_eq!(dump[2], 20);
    }
}
