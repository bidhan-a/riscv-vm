use anyhow::{Result, bail};

/// RISC-V instruction formats
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionFormat {
    R,
    I,
    S,
    B,
    U,
    J,
}

/// Decoded RISC-V instruction
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInstruction {
    pub format: InstructionFormat,
    pub opcode: u8,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub funct3: u8,
    pub funct7: u8,
    pub imm: i64,
    pub raw: u32,
}

impl DecodedInstruction {
    /// Decode a 32-bit instruction into DecodedInstruction
    pub fn new(instruction: u32) -> Result<Self> {
        let opcode = (instruction & 0x7F) as u8;
        let format = Self::determine_format(opcode)?;
        match format {
            InstructionFormat::R => Self::decode_r_type(instruction),
            InstructionFormat::I => Self::decode_i_type(instruction),
            InstructionFormat::S => Self::decode_s_type(instruction),
            InstructionFormat::B => Self::decode_b_type(instruction),
            InstructionFormat::U => Self::decode_u_type(instruction),
            InstructionFormat::J => Self::decode_j_type(instruction),
        }
    }

    // Determine instruction format from opcode
    fn determine_format(opcode: u8) -> Result<InstructionFormat> {
        match opcode {
            0x33 | 0x3B => Ok(InstructionFormat::R),
            0x03 | 0x13 | 0x1B | 0x67 | 0x73 => Ok(InstructionFormat::I),
            0x23 => Ok(InstructionFormat::S),
            0x63 => Ok(InstructionFormat::B),
            0x17 | 0x37 => Ok(InstructionFormat::U),
            0x6F => Ok(InstructionFormat::J),
            _ => bail!("Unknown opcode: 0x{:02X}", opcode),
        }
    }

    // Decode R-type instructions
    //
    //  31        25 24    20 19    15 14  12 11     7 6      0
    // ┌────────────┬────────┬────────┬──────┬────────┬────────┐
    // │   funct7   │  rs2   │  rs1   │funct3│   rd   │ opcode │
    // │   7 bits   │ 5 bits │ 5 bits │3 bits│ 5 bits │ 7 bits │
    // └────────────┴────────┴────────┴──────┴────────┴────────┘
    //
    fn decode_r_type(instruction: u32) -> Result<Self> {
        // Extract opcode
        let opcode = (instruction & 0x7F) as u8;

        // Extract rd
        let rd = ((instruction >> 7) & 0x1F) as u8;

        // Extract funct3
        let funct3 = ((instruction >> 12) & 0x7) as u8;

        // Extract rs1
        let rs1 = ((instruction >> 15) & 0x1F) as u8;

        // Extract rs2
        let rs2 = ((instruction >> 20) & 0x1F) as u8;

        // Extract funct7
        let funct7 = ((instruction >> 25) & 0x7F) as u8;

        // No imm value
        let imm = 0;

        Ok(DecodedInstruction {
            format: InstructionFormat::R,
            opcode,
            rd,
            rs1,
            rs2,
            funct3,
            funct7,
            imm,
            raw: instruction,
        })
    }

    // Decode I-type instructions
    //
    //  31                    20 19    15 14  12 11     7 6      0
    // ┌────────────────────────┬────────┬──────┬────────┬────────┐
    // │      immediate         │  rs1   │funct3│   rd   │ opcode │
    // │       12 bits          │ 5 bits │3 bits│ 5 bits │ 7 bits │
    // └────────────────────────┴────────┴──────┴────────┴────────┘
    //
    fn decode_i_type(instruction: u32) -> Result<Self> {
        // Extract opcode
        let opcode = (instruction & 0x7F) as u8;

        // Extract rd
        let rd = ((instruction >> 7) & 0x1F) as u8;

        // Extract funct3
        let funct3 = ((instruction >> 12) & 0x7) as u8;

        // Extract rs1
        let rs1 = ((instruction >> 15) & 0x1F) as u8;

        // Extract imm
        let imm = sign_extend((instruction >> 20) & 0xFFF, 12);

        Ok(DecodedInstruction {
            format: InstructionFormat::I,
            opcode,
            rd,
            rs1,
            rs2: 0,
            funct3,
            funct7: 0,
            imm,
            raw: instruction,
        })
    }

    // Decode S-type instructions
    //
    //  31        25 24    20 19    15 14  12 11     7 6      0
    // ┌────────────┬────────┬────────┬──────┬────────┬────────┐
    // │  imm[11:5] │  rs2   │  rs1   │funct3│imm[4:0]│ opcode │
    // │   7 bits   │ 5 bits │ 5 bits │3 bits│ 5 bits │ 7 bits │
    // └────────────┴────────┴────────┴──────┴────────┴────────┘
    //
    fn decode_s_type(instruction: u32) -> Result<Self> {
        // Extract opcode
        let opcode = (instruction & 0x7F) as u8;

        // Extract imm[4:0]
        let imm_4_0 = (instruction >> 7) & 0x1F;

        // Extract funct3
        let funct3 = ((instruction >> 12) & 0x7) as u8;

        // Extract rs1
        let rs1 = ((instruction >> 15) & 0x1F) as u8;

        // Extract rs2
        let rs2 = ((instruction >> 20) & 0x1F) as u8;

        // Extract imm[11:5]
        let imm_11_5 = (instruction >> 25) & 0x7F;

        // Combine immediate
        let imm = sign_extend(imm_11_5 << 5 | imm_4_0, 12);

        Ok(DecodedInstruction {
            format: InstructionFormat::S,
            opcode,
            rd: 0,
            rs1,
            rs2,
            funct3,
            funct7: 0,
            imm,
            raw: instruction,
        })
    }

    // Decode B-type instructions
    //
    //  31  30        25 24    20 19    15 14  12 11  8   7 6      0
    // ┌────┬──────────┬────────┬────────┬──────┬─────┬────┬────────┐
    // │imm │ imm[10:5]│  rs2   │  rs1   │funct3│imm  │imm │ opcode │
    // │[12]│  6 bits  │ 5 bits │ 5 bits │3 bits│[4:1]│[11]│ 7 bits │
    // └────┴──────────┴────────┴────────┴──────┴─────┴────┴────────┘
    //
    fn decode_b_type(instruction: u32) -> Result<Self> {
        // Extract opcode
        let opcode = (instruction & 0x7F) as u8;

        // Extract imm[11]
        let imm_11 = (instruction >> 7) & 0x1;

        // Extract imm[4:1]
        let imm_4_1 = (instruction >> 8) & 0xF;

        // Extract funct3
        let funct3 = ((instruction >> 12) & 0x7) as u8;

        // Exract rs1
        let rs1 = ((instruction >> 15) & 0x1F) as u8;

        // Extract rs2
        let rs2 = ((instruction >> 20) & 0x1F) as u8;

        // Extract imm[10:5]
        let imm_10_5 = (instruction >> 25) & 0x3F;

        // Extract imm[12]
        let imm_12 = (instruction >> 30) & 0x1;

        // Combine immediate
        let imm = sign_extend(
            (imm_12 << 12) | (imm_11 << 11) | (imm_10_5 << 5) | (imm_4_1 << 1),
            13,
        );

        Ok(DecodedInstruction {
            format: InstructionFormat::B,
            opcode,
            rd: 0,
            rs1,
            rs2,
            funct3,
            funct7: 0,
            imm,
            raw: instruction,
        })
    }

    // Decode U-type instructions
    //
    //  31                                  12 11      7 6      0
    // ┌───────────────────────────────────────┬────────┬────────┐
    // │            immediate[31:12]           │   rd   │ opcode │
    // │               20 bits                 │ 5 bits │ 7 bits │
    // └───────────────────────────────────────┴────────┴────────┘
    //
    fn decode_u_type(instruction: u32) -> Result<Self> {
        // Extract opcode
        let opcode = (instruction & 0x7F) as u8;

        // Extract rd
        let rd = ((instruction >> 7) & 0x1F) as u8;

        // Extract immediate
        let imm = sign_extend(instruction & 0xFFFFF000, 32);

        Ok(DecodedInstruction {
            format: InstructionFormat::U,
            opcode,
            rd,
            rs1: 0,
            rs2: 0,
            funct3: 0,
            funct7: 0,
            imm,
            raw: instruction,
        })
    }

    // Decode J-type instructions
    //
    //  31  30          21 20  19          12 11     7 6        0
    // ┌────┬──────────────┬────┬─────────────┬────────┬────────┐
    // │imm │  imm[10:1]   │imm │ imm[19:12]  │   rd   │ opcode │
    // │[20]│   10 bits    │[11]│ 8 bits      │ 5 bits │ 7 bits │
    // └────┴──────────────┴────┴─────────────┴────────┴────────┘
    //
    fn decode_j_type(instruction: u32) -> Result<Self> {
        // Extract opcode
        let opcode = (instruction & 0x7F) as u8;

        // Extract rd
        let rd = ((instruction >> 7) & 0x1F) as u8;

        // Extract imm[19:12]
        let imm_19_12 = (instruction >> 12) & 0xFF;

        // Extract imm[11]
        let imm_11 = (instruction >> 20) & 0x1;

        // Extract imm[10:1]
        let imm_10_1 = (instruction >> 21) & 0x3FF;

        // Extract imm[20]
        let imm_20 = (instruction >> 31) & 0x1;

        // Combine immediate
        let imm = sign_extend(
            (imm_20 << 20) | (imm_19_12 << 12) | (imm_11 << 11) | (imm_10_1 << 1),
            21,
        );

        Ok(DecodedInstruction {
            format: InstructionFormat::J,
            opcode,
            rd,
            rs1: 0,
            rs2: 0,
            funct3: 0,
            funct7: 0,
            imm,
            raw: instruction,
        })
    }
}

// Extend a value from N bits to 64 bits, preserving sign
fn sign_extend(value: u32, bits: u8) -> i64 {
    let shift = 64 - bits;
    ((value as i64) << shift) >> shift
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_determine_format() {
        // R-type
        assert_eq!(
            DecodedInstruction::determine_format(0x33).unwrap(),
            InstructionFormat::R
        );

        // I-type
        assert_eq!(
            DecodedInstruction::determine_format(0x13).unwrap(),
            InstructionFormat::I
        );

        // S-type
        assert_eq!(
            DecodedInstruction::determine_format(0x23).unwrap(),
            InstructionFormat::S
        );

        // B-type
        assert_eq!(
            DecodedInstruction::determine_format(0x63).unwrap(),
            InstructionFormat::B
        );

        // U-type
        assert_eq!(
            DecodedInstruction::determine_format(0x37).unwrap(),
            InstructionFormat::U
        );

        // J-type
        assert_eq!(
            DecodedInstruction::determine_format(0x6F).unwrap(),
            InstructionFormat::J
        );
    }

    #[test]
    fn test_determine_format_invalid() {
        assert!(DecodedInstruction::determine_format(0xFF).is_err());
    }

    #[test]
    fn test_decode_r_type() {
        // ADD x3, x1, x2
        // opcode=0x33, rd=3, funct3=0, rs1=1, rs2=2, funct7=0
        let instruction = 0x002081B3;

        let decoded = DecodedInstruction::new(instruction).unwrap();

        assert_eq!(decoded.format, InstructionFormat::R);
        assert_eq!(decoded.opcode, 0x33);
        assert_eq!(decoded.rd, 3);
        assert_eq!(decoded.funct3, 0);
        assert_eq!(decoded.rs1, 1);
        assert_eq!(decoded.rs2, 2);
        assert_eq!(decoded.funct7, 0);
        assert_eq!(decoded.imm, 0);
        assert_eq!(decoded.raw, instruction);
    }

    #[test]
    fn test_decode_i_type() {
        // ADDI x1, x2, 100
        // opcode=0x13, rd=1, funct3=0, rs1=2, imm=100
        let instruction = 0x06410093;

        let decoded = DecodedInstruction::new(instruction).unwrap();

        assert_eq!(decoded.format, InstructionFormat::I);
        assert_eq!(decoded.opcode, 0x13);
        assert_eq!(decoded.rd, 1);
        assert_eq!(decoded.funct3, 0);
        assert_eq!(decoded.rs1, 2);
        assert_eq!(decoded.imm, 100);
    }

    #[test]
    fn test_decode_s_type() {
        // SW x5, 8(x6)
        // opcode=0x23, funct3=2, rs1=6, rs2=5, imm=8
        let instruction = 0x00532423;

        let decoded = DecodedInstruction::new(instruction).unwrap();

        assert_eq!(decoded.format, InstructionFormat::S);
        assert_eq!(decoded.opcode, 0x23);
        assert_eq!(decoded.funct3, 2);
        assert_eq!(decoded.rs1, 6);
        assert_eq!(decoded.rs2, 5);
        assert_eq!(decoded.imm, 8);
    }

    #[test]
    fn test_decode_b_type() {
        // BEQ x1, x2, 16
        // opcode=0x63, funct3=0, rs1=1, rs2=2, imm=16
        let instruction = 0x00208863;

        let decoded = DecodedInstruction::new(instruction).unwrap();

        assert_eq!(decoded.format, InstructionFormat::B);
        assert_eq!(decoded.opcode, 0x63);
        assert_eq!(decoded.funct3, 0);
        assert_eq!(decoded.rs1, 1);
        assert_eq!(decoded.rs2, 2);
        assert_eq!(decoded.imm, 16);
    }

    #[test]
    fn test_decode_u_type() {
        // LUI x1, 0x12345
        // opcode=0x37, rd=1, imm=0x12345000
        let instruction = 0x123450B7;

        let decoded = DecodedInstruction::new(instruction).unwrap();

        assert_eq!(decoded.format, InstructionFormat::U);
        assert_eq!(decoded.opcode, 0x37);
        assert_eq!(decoded.rd, 1);
        assert_eq!(decoded.imm, 0x12345000);
    }

    #[test]
    fn test_decode_j_type() {
        // JAL x1, 1024
        // opcode=0x6F, rd=1, imm=1024
        let instruction = 0x400000EF;

        let decoded = DecodedInstruction::new(instruction).unwrap();

        assert_eq!(decoded.format, InstructionFormat::J);
        assert_eq!(decoded.opcode, 0x6F);
        assert_eq!(decoded.rd, 1);
        assert_eq!(decoded.imm, 1024);
    }
}
