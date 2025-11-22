use crate::{Memory, Registers};
use anyhow::Result;

/// RISC-V privilege modes
///
/// RISC-V has three privilege levels:
/// - Machine (M): Highest privilege, firmware/bootloader
/// - Supervisor (S): OS kernel
/// - User (U): Applications (lowest privilege)
///
/// Only Machine mode is supported for now.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PrivilegeMode {
    User = 0,       // U-mode: Unprivileged
    Supervisor = 1, // S-mode: OS kernel (future)
    #[default]
    Machine = 3, // M-mode: Firmware/bootloader
}

/// The CPU Core for RISC-V VM
///
/// Integrates all components needed to execute RISC-V instructions:
/// - Registers
/// - Memory subsystem
/// - Program Counter
/// - Privilege mode
/// - CSR (Control & Status Registers)
#[derive(Debug, Clone)]
pub struct CPU {
    /// General-purpose registers (x0-x31)
    pub registers: Registers,

    /// Byte-addressable memory
    pub memory: Memory,

    /// Program Counter
    pub pc: u64,

    /// Current privilege mode
    pub mode: PrivilegeMode,
    // TODO: CSR (Control & Status Registers)
    // csr: CSR,
}

impl CPU {
    /// Create a new CPU instance with specified memory size in bytes
    pub fn new(memory_size: usize) -> Self {
        Self {
            registers: Registers::new(),
            memory: Memory::new(memory_size),
            pc: 0,
            mode: PrivilegeMode::Machine,
        }
    }

    /// Get current Program Counter (PC) value
    pub fn pc(&self) -> u64 {
        self.pc
    }

    /// Set Program Counter (PC) to a new value
    pub fn set_pc(&mut self, new_pc: u64) {
        self.pc = new_pc;
    }

    /// Get current privilege mode
    pub fn mode(&self) -> PrivilegeMode {
        self.mode
    }

    /// Set current privilege mode
    pub fn set_mode(&mut self, new_mode: PrivilegeMode) {
        self.mode = new_mode;
    }

    /// Reset CPU to initial state
    pub fn reset(&mut self) {
        self.registers.reset();
        self.memory.reset();
        self.pc = 0;
        self.mode = PrivilegeMode::Machine;
    }

    /// Fetch next instruction from memory at current PC
    /// First step of fetch-decode-execute cycle.
    pub fn fetch(&self) -> Result<u32> {
        let ix = self.memory.read_u32(self.pc)?;
        Ok(ix)
    }

    // TODO:
    // - decode(&self, instruction: u32) -> DecodedInstruction
    // - execute(&mut self, decoded: DecodedInstruction) -> Result<()>
    // - step(&mut self) -> Result<()>  (one fetch-decode-execute cycle)
    // - run(&mut self) -> Result<i32>  (execute until program exits)
}

impl Default for CPU {
    fn default() -> Self {
        Self::new(1024 * 1024) // 1 MB default memory
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_new() {
        let cpu = CPU::new(1024);

        // Verify memory size
        assert_eq!(cpu.memory.size(), 1024);

        // Verify PC starts at 0
        assert_eq!(cpu.pc(), 0);

        // Verify we boot in Machine mode
        assert_eq!(cpu.mode(), PrivilegeMode::Machine);

        // Verify all registers are 0
        for i in 0..32 {
            assert_eq!(cpu.registers.read(i), 0);
        }
    }

    #[test]
    fn test_pc_operations() {
        let mut cpu = CPU::new(1024);

        // Initial PC should be 0
        assert_eq!(cpu.pc(), 0);

        // Set PC to entry point
        cpu.set_pc(0x80000000);
        assert_eq!(cpu.pc(), 0x80000000);

        // Set PC to different address
        cpu.set_pc(0x1000);
        assert_eq!(cpu.pc(), 0x1000);

        // PC can be set to any valid address
        cpu.set_pc(u64::MAX);
        assert_eq!(cpu.pc(), u64::MAX);
    }

    #[test]
    fn test_privilege_mode() {
        let mut cpu = CPU::new(1024);

        // Should boot in Machine mode
        assert_eq!(cpu.mode(), PrivilegeMode::Machine);

        // Can transition to Supervisor
        cpu.set_mode(PrivilegeMode::Supervisor);
        assert_eq!(cpu.mode(), PrivilegeMode::Supervisor);

        // Can transition to User
        cpu.set_mode(PrivilegeMode::User);
        assert_eq!(cpu.mode(), PrivilegeMode::User);

        // Can transition back to Machine
        cpu.set_mode(PrivilegeMode::Machine);
        assert_eq!(cpu.mode(), PrivilegeMode::Machine);
    }

    #[test]
    fn test_privilege_mode_values() {
        // Verify privilege mode encoding matches RISC-V spec
        assert_eq!(PrivilegeMode::User as u8, 0);
        assert_eq!(PrivilegeMode::Supervisor as u8, 1);
        assert_eq!(PrivilegeMode::Machine as u8, 3);

        // Verify default is Machine
        assert_eq!(PrivilegeMode::default(), PrivilegeMode::Machine);
    }

    #[test]
    fn test_cpu_reset() {
        let mut cpu = CPU::new(1024);

        // Modify CPU state
        cpu.set_pc(0x1234);
        cpu.set_mode(PrivilegeMode::User);
        cpu.registers.write(1, 0xDEADBEEF);
        cpu.memory.write_u32(0x100, 0xCAFEBABE).unwrap();

        // Reset CPU
        cpu.reset();

        // Verify everything is reset
        assert_eq!(cpu.pc(), 0);
        assert_eq!(cpu.mode(), PrivilegeMode::Machine);
        assert_eq!(cpu.registers.read(1), 0);
        assert_eq!(cpu.memory.read_u32(0x100).unwrap(), 0);
    }

    #[test]
    fn test_fetch_instruction() {
        let mut cpu = CPU::new(1024);

        // Write an instruction to memory
        // ADDI x1, x0, 5 encoded as: 0x00500093
        cpu.memory.write_u32(0, 0x00500093).unwrap();

        // Fetch should read the instruction
        let instruction = cpu.fetch().unwrap();
        assert_eq!(instruction, 0x00500093);
    }

    #[test]
    fn test_fetch_different_pc() {
        let mut cpu = CPU::new(1024);

        // Write instructions at different locations
        cpu.memory.write_u32(0, 0x11111111).unwrap();
        cpu.memory.write_u32(4, 0x22222222).unwrap();
        cpu.memory.write_u32(8, 0x33333333).unwrap();

        // Fetch from different PCs
        cpu.set_pc(0);
        assert_eq!(cpu.fetch().unwrap(), 0x11111111);

        cpu.set_pc(4);
        assert_eq!(cpu.fetch().unwrap(), 0x22222222);

        cpu.set_pc(8);
        assert_eq!(cpu.fetch().unwrap(), 0x33333333);
    }

    #[test]
    fn test_fetch_out_of_bounds() {
        let cpu = CPU::new(1024);

        // Try to fetch beyond memory bounds
        // PC at 1024 would try to read bytes 1024-1027, which is out of bounds
        let mut cpu_test = cpu.clone();
        cpu_test.set_pc(1024);
        assert!(cpu_test.fetch().is_err());

        // Way out of bounds.
        cpu_test.set_pc(0x100000);
        assert!(cpu_test.fetch().is_err());
    }

    #[test]
    fn test_registers_memory_integration() {
        let mut cpu = CPU::new(1024);

        // Can write to registers
        cpu.registers.write(1, 0x1000);
        assert_eq!(cpu.registers.read(1), 0x1000);

        // Can write to memory
        cpu.memory.write_u64(0x100, 0xDEADBEEFCAFEBABE).unwrap();
        assert_eq!(cpu.memory.read_u64(0x100).unwrap(), 0xDEADBEEFCAFEBABE);

        // x0 is hardwired to 0
        cpu.registers.write(0, 999);
        assert_eq!(cpu.registers.read(0), 0);
    }
}
