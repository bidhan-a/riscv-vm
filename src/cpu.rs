use crate::{DecodedInstruction, Memory, Registers};
use anyhow::{Result, bail};

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

    /// Execute a complete instruction cycle
    pub fn step(&mut self) -> Result<()> {
        let instruction = self.fetch()?;
        let decoded_instruction = DecodedInstruction::new(instruction)?;
        self.execute(&decoded_instruction)
    }

    /// Execute a decoded instruction by dispatching to specific handlers
    pub fn execute(&mut self, instruction: &DecodedInstruction) -> Result<()> {
        match instruction.opcode {
            0x37 => self.execute_lui(instruction),

            0x17 => self.execute_auipc(instruction),

            0x13 => match instruction.funct3 {
                0b000 => self.execute_addi(instruction),
                0b010 => self.execute_slti(instruction),
                0b011 => self.execute_sltiu(instruction),
                0b100 => self.execute_xori(instruction),
                0b110 => self.execute_ori(instruction),
                0b111 => self.execute_andi(instruction),
                0b001 => self.execute_slli(instruction),
                0b101 => {
                    // srli or srai distinguished by imm[11:6]
                    // srli: 0b000000 (0x00)
                    // srai: 0b010000 (0x10)
                    if (instruction.imm >> 6) & 0x3F == 0x00 {
                        self.execute_srli(instruction)
                    } else {
                        self.execute_srai(instruction)
                    }
                }
                _ => bail!("Unknown funct3 for opcode 0x13: {}", instruction.funct3),
            },

            0x33 => match (instruction.funct3, instruction.funct7) {
                (0b000, 0x00) => self.execute_add(instruction),
                (0b000, 0x20) => self.execute_sub(instruction),
                (0b001, 0x00) => self.execute_sll(instruction),
                (0b010, 0x00) => self.execute_slt(instruction),
                (0b011, 0x00) => self.execute_sltu(instruction),
                (0b100, 0x00) => self.execute_xor(instruction),
                (0b101, 0x00) => self.execute_srl(instruction),
                (0b101, 0x20) => self.execute_sra(instruction),
                (0b110, 0x00) => self.execute_or(instruction),
                (0b111, 0x00) => self.execute_and(instruction),
                _ => bail!(
                    "Unknown (funct3, funct7) for opcode 0x33: ({}, {})",
                    instruction.funct3,
                    instruction.funct7
                ),
            },

            0x0F => match instruction.funct3 {
                0b000 => self.execute_fence(instruction),
                0b001 => self.execute_fence_i(instruction),
                _ => bail!("Unknown funct3 for opcode 0x0F: {}", instruction.funct3),
            },

            0x73 => match instruction.funct3 {
                0b001 => self.execute_csrrw(instruction),
                0b010 => self.execute_csrrs(instruction),
                0b011 => self.execute_csrrc(instruction),
                0b101 => self.execute_csrrwi(instruction),
                0b110 => self.execute_csrrsi(instruction),
                0b111 => self.execute_csrrci(instruction),
                0b000 => {
                    match instruction.imm as u32 & 0xFFF {
                        0x000 => self.execute_ecall(instruction),
                        0x001 => self.execute_ebreak(instruction),
                        0x102 => self.execute_sret(instruction),
                        0x302 => self.execute_mret(instruction),
                        0x105 => self.execute_wfi(instruction),
                        _ => bail!(
                            "Unknown imm for opcode 0x73 and funct3 0b000: {}",
                            instruction.imm
                        ),
                    }

                    // TODO: sfence.vma
                }
                _ => bail!("Unknown funct3 for opcode 0x73: {}", instruction.funct3),
            },

            0x03 => match instruction.funct3 {
                0b000 => self.execute_lb(instruction),
                0b001 => self.execute_lh(instruction),
                0b010 => self.execute_lw(instruction),
                0b011 => self.execute_ld(instruction), // RV64I only
                0b100 => self.execute_lbu(instruction),
                0b101 => self.execute_lhu(instruction),
                0b110 => self.execute_lwu(instruction), // RV64I only
                _ => bail!("Unknown funct3 for opcode 0x03: {}", instruction.funct3),
            },

            0x23 => match instruction.funct3 {
                0b000 => self.execute_sb(instruction),
                0b001 => self.execute_sh(instruction),
                0b010 => self.execute_sw(instruction),
                0b011 => self.execute_sd(instruction), // RV64I only
                _ => bail!("Unknown funct3 for opcode 0x32: {}", instruction.funct3),
            },

            0x6F => self.execute_jal(instruction),

            0x67 => self.execute_jalr(instruction),

            0x63 => match instruction.funct3 {
                0b000 => self.execute_beq(instruction),
                0b001 => self.execute_bne(instruction),
                0b100 => self.execute_blt(instruction),
                0b101 => self.execute_bge(instruction),
                0b110 => self.execute_bltu(instruction),
                0b111 => self.execute_bgeu(instruction),
                _ => bail!("Unknown funct3 for opcode 0x63: {}", instruction.funct3),
            },

            0x1B => match instruction.funct3 {
                0b000 => self.execute_addiw(instruction),
                0b001 => self.execute_slliw(instruction),
                0b101 => {
                    // srliw or sraiw distinguished by imm[11:5]
                    if (instruction.imm >> 5) & 0x7F == 0x00 {
                        self.execute_srliw(instruction)
                    } else {
                        self.execute_sraiw(instruction)
                    }
                }
                _ => bail!("Unknown funct3 for opcode 0x1B: {}", instruction.funct3),
            },

            0x3B => match (instruction.funct3, instruction.funct7) {
                (0b000, 0x00) => self.execute_addw(instruction),
                (0b000, 0x20) => self.execute_subw(instruction),
                (0b001, 0x00) => self.execute_sllw(instruction),
                (0b101, 0x00) => self.execute_srlw(instruction),
                (0b101, 0x20) => self.execute_sraw(instruction),
                _ => bail!(
                    "Unknown (funct3, funct7) for opcode 0x3B: ({}, {})",
                    instruction.funct3,
                    instruction.funct7
                ),
            },

            _ => bail!("Unknown opcode: {}", instruction.opcode),
        }
    }

    fn execute_lui(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lui")
    }

    fn execute_auipc(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("aupic")
    }

    // Execute addi instruction
    // Format: addi rd, rs1, imm
    // Specification: x[rd] = x[rs1] + sext(immediate)
    fn execute_addi(&mut self, inst: &DecodedInstruction) -> Result<()> {
        let rs1_value = self.registers.read(inst.rs1);
        let result = rs1_value.wrapping_add(inst.imm as u64);
        self.registers.write(inst.rd, result);
        self.pc += 4;
        Ok(())
    }

    fn execute_slti(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("slti")
    }
    fn execute_sltiu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sltiu")
    }
    fn execute_xori(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("xori")
    }
    fn execute_ori(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("ori")
    }
    fn execute_andi(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("andi")
    }
    fn execute_slli(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("slli")
    }
    fn execute_srli(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("srli")
    }
    fn execute_srai(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("srai")
    }

    // Execute add instruction
    // Format: add rd, rs1, rs2
    // Specification: x[rd] = x[rs1] + x[rs2]
    fn execute_add(&mut self, inst: &DecodedInstruction) -> Result<()> {
        let rs1_value = self.registers.read(inst.rs1);
        let rs2_value = self.registers.read(inst.rs2);
        let result = rs1_value.wrapping_add(rs2_value);
        self.registers.write(inst.rd, result);
        self.pc += 4;
        Ok(())
    }

    // Execute sub instruction
    // Format: sub rd, rs1, rs2
    // Specification: x[rd] = x[rs1] - x[rs2]
    fn execute_sub(&mut self, inst: &DecodedInstruction) -> Result<()> {
        let rs1_value = self.registers.read(inst.rs1);
        let rs2_value = self.registers.read(inst.rs2);
        let result = rs1_value.wrapping_sub(rs2_value);
        self.registers.write(inst.rd, result);
        self.pc += 4;
        Ok(())
    }

    fn execute_sll(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sll")
    }
    fn execute_slt(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("slt")
    }
    fn execute_sltu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sltu")
    }
    fn execute_xor(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("xor")
    }
    fn execute_srl(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("srl")
    }
    fn execute_sra(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sra")
    }
    fn execute_or(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("or")
    }
    fn execute_and(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("and")
    }
    fn execute_fence(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("fence")
    }
    fn execute_fence_i(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("fence.i")
    }
    fn execute_csrrw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("csrrw")
    }
    fn execute_csrrs(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("csrrs")
    }
    fn execute_csrrc(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("csrrc")
    }
    fn execute_csrrwi(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("csrrwi")
    }
    fn execute_csrrsi(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("csrrsi")
    }
    fn execute_csrrci(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("csrrci")
    }

    fn execute_ecall(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("ecall")
    }
    fn execute_ebreak(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("ebreak")
    }
    fn execute_sret(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sret")
    }
    fn execute_mret(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("mret")
    }
    fn execute_wfi(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("wfi")
    }
    fn execute_lb(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lb")
    }
    fn execute_lh(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lh")
    }
    fn execute_lw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lw")
    }
    fn execute_ld(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("ld")
    }
    fn execute_lbu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lbu")
    }
    fn execute_lhu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lhu")
    }
    fn execute_lwu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("lwu")
    }
    fn execute_sb(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sb")
    }
    fn execute_sh(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sh")
    }
    fn execute_sw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sw")
    }
    fn execute_sd(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sd")
    }
    fn execute_jal(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("jal")
    }
    fn execute_jalr(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("jalr")
    }
    fn execute_beq(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("beq")
    }
    fn execute_bne(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("bne")
    }
    fn execute_blt(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("blt")
    }
    fn execute_bge(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("bge")
    }
    fn execute_bltu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("bltu")
    }
    fn execute_bgeu(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("bgeu")
    }
    fn execute_addiw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("addiw")
    }
    fn execute_slliw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("slliw")
    }
    fn execute_srliw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("srliw")
    }
    fn execute_sraiw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sraiw")
    }
    fn execute_addw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("addw")
    }
    fn execute_subw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("subw")
    }
    fn execute_sllw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sllw")
    }
    fn execute_srlw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("srlw")
    }
    fn execute_sraw(&mut self, _inst: &DecodedInstruction) -> Result<()> {
        todo!("sraw")
    }
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

    #[test]
    fn test_addi_positive() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, 10);
        cpu.memory.write_u32(0, 0x00508113).unwrap(); // addi x2, x1, 5
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(2), 15);
        assert_eq!(cpu.pc(), 4);
    }

    #[test]
    fn test_addi_negative() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, 10);
        cpu.memory.write_u32(0, 0xFFD08113).unwrap(); // addi x2, x1, -3
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(2), 7);
    }

    #[test]
    fn test_addi_overflow() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, u64::MAX);
        cpu.memory.write_u32(0, 0x00108113).unwrap(); // addi x2, x1, 1 
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(2), 0); // Overflow wraps
    }

    #[test]
    fn test_add_positive() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, 10);
        cpu.registers.write(2, 20);
        cpu.memory.write_u32(0, 0x002081B3).unwrap(); // add x3, x1, x2
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(3), 30);
        assert_eq!(cpu.pc(), 4);
    }

    #[test]
    fn test_add_negative() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, 10);
        cpu.registers.write(2, (-5i64) as u64);
        cpu.memory.write_u32(0, 0x002081B3).unwrap(); // add x3, x1, x2 
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(3), 5);
    }

    #[test]
    fn test_add_overflow() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, u64::MAX);
        cpu.registers.write(2, 1);
        cpu.memory.write_u32(0, 0x002081B3).unwrap(); // add x3, x1, x2
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(3), 0); // Overflow wraps
    }

    #[test]
    fn test_sub_positive_result() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, 30);
        cpu.registers.write(2, 10);
        cpu.memory.write_u32(0, 0x402081B3).unwrap(); // sub x3, x1, x2
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(3), 20);
        assert_eq!(cpu.pc(), 4);
    }

    #[test]
    fn test_sub_negative_result() {
        let mut cpu = CPU::new(1024);

        cpu.registers.write(1, 10);
        cpu.registers.write(2, 30);
        cpu.memory.write_u32(0, 0x402081B3).unwrap(); // sub x3, x1, x2
        cpu.step().unwrap();

        assert_eq!(cpu.registers.read(3) as i64, -20);
    }

    #[test]
    fn test_step_multiple_instructions() {
        let mut cpu = CPU::new(1024);

        cpu.memory.write_u32(0, 0x00500093).unwrap(); // addi x1, x0, 5
        cpu.memory.write_u32(4, 0x00A00113).unwrap(); // addi x2, x0, 10
        cpu.memory.write_u32(8, 0x002081B3).unwrap(); // add x3, x1, x2

        // execute first instruction
        cpu.step().unwrap();
        assert_eq!(cpu.registers.read(1), 5);
        assert_eq!(cpu.pc(), 4);

        // execute second instruction
        cpu.step().unwrap();
        assert_eq!(cpu.registers.read(2), 10);
        assert_eq!(cpu.pc(), 8);

        // execute third instruction
        cpu.step().unwrap();
        assert_eq!(cpu.registers.read(3), 15);
        assert_eq!(cpu.pc(), 12);
    }
}
