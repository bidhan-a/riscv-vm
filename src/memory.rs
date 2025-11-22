use anyhow::{Ok, Result, bail};

/// A byte-addressable memory system with little-endian byte ordering,
/// supporting all RISC-V load/store sizes (8, 16, 32, 64-bit).
#[derive(Debug, Clone)]
pub struct Memory {
    data: Vec<u8>,
    size: usize,
}

impl Memory {
    /// Create a new Memory instance with the given size in bytes
    pub fn new(size: usize) -> Self {
        assert!(size > 0, "Memory size must be greater than 0");
        Self {
            data: vec![0; size],
            size,
        }
    }

    /// Read a single byte from memory at the specified address
    /// Used by LB/LBU instructions
    pub fn read_u8(&self, addr: u64) -> Result<u8> {
        let addr_usize = addr as usize;
        if addr_usize >= self.size {
            bail!(
                "Memory read out of bounds: address 0x{:x} >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }
        Ok(self.data[addr_usize])
    }

    /// Write a single byte to memory at the specified address
    /// Used by SB instruction
    pub fn write_u8(&mut self, addr: u64, value: u8) -> Result<()> {
        let addr_usize = addr as usize;
        if addr_usize >= self.size {
            bail!(
                "Memory write out of bounds: address 0x{:x} > size 0x{:x}",
                addr_usize,
                self.size
            );
        }
        self.data[addr_usize] = value;
        Ok(())
    }

    /// Read 2 bytes (16-bit halfword) from memory in little-endian order
    /// Used by LH/LHU instructions
    pub fn read_u16(&self, addr: u64) -> Result<u16> {
        let addr_usize = addr as usize;
        if addr_usize + 1 >= self.size {
            bail!(
                "Memory read out of bounds: address 0x{:x} + 1 >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }
        let mut bytes = [0u8; 2];
        bytes.copy_from_slice(&self.data[addr_usize..addr_usize + 2]);
        let result = u16::from_le_bytes(bytes);
        Ok(result)
    }

    /// Write 2 bytes (16-bit halfword) to memory in little-endian order
    /// Used by SH instruction
    pub fn write_u16(&mut self, addr: u64, value: u16) -> Result<()> {
        let addr_usize = addr as usize;
        if addr_usize + 1 >= self.size {
            bail!(
                "Memory write out of bounds: address 0x{:x} + 1 >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }

        let bytes = value.to_le_bytes();
        self.data[addr_usize..addr_usize + 2].copy_from_slice(&bytes);
        Ok(())
    }

    /// Read 4 bytes (32-bit word) from memory in little-endian order
    /// Used by LW/LWU instructions
    pub fn read_u32(&self, addr: u64) -> Result<u32> {
        let addr_usize = addr as usize;
        if addr_usize + 3 >= self.size {
            bail!(
                "Memory read out of bounds: address 0x{:x} + 3 >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&self.data[addr_usize..addr_usize + 4]);
        let result = u32::from_le_bytes(bytes);
        Ok(result)
    }

    /// Write 4 bytes (32-bit word) to memory in little-endian order
    /// Used by SW instruction and instruction fetch
    pub fn write_u32(&mut self, addr: u64, value: u32) -> Result<()> {
        let addr_usize = addr as usize;
        if addr_usize + 3 >= self.size {
            bail!(
                "Memory write out of bounds: address 0x{:x} + 3 >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }

        let bytes = value.to_le_bytes();
        self.data[addr_usize..addr_usize + 4].copy_from_slice(&bytes);

        Ok(())
    }

    /// Read 8 bytes (64-bit doubleword) from memory in little-endian order
    /// Used by LD instruction
    pub fn read_u64(&self, addr: u64) -> Result<u64> {
        let addr_usize = addr as usize;
        if addr_usize + 7 >= self.size {
            bail!(
                "Memory read out of bounds: address 0x{:x} + 7 >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.data[addr_usize..addr_usize + 8]);
        let result = u64::from_le_bytes(bytes);
        Ok(result)
    }

    /// Write 8 bytes (64-bit doubleword) to memory in little-endian order
    /// Used by SD instruction
    pub fn write_u64(&mut self, addr: u64, value: u64) -> Result<()> {
        let addr_usize = addr as usize;
        if addr_usize + 7 >= self.size {
            bail!(
                "Memory write out of bounds: address 0x{:x} + 7 >= size 0x{:x}",
                addr_usize,
                self.size
            );
        }

        let bytes = value.to_le_bytes();
        self.data[addr_usize..addr_usize + 8].copy_from_slice(&bytes);

        Ok(())
    }

    /// Read multiple bytes from memory
    /// Used for debugging and memory inspection
    pub fn read_bytes(&self, addr: u64, len: usize) -> Result<Vec<u8>> {
        let addr_usize = addr as usize;
        if addr_usize + len >= self.size {
            bail!(
                "Memory read out of bounds: address 0x{:x} + length {} > size 0x{:x}",
                addr_usize,
                len,
                self.size
            );
        }

        let mut bytes = vec![0u8; len];
        bytes.copy_from_slice(&self.data[addr_usize..addr_usize + len]);
        Ok(bytes)
    }

    /// Write multiple bytes to memory (for program loading)
    /// Used by ELF loader to load program sections
    pub fn write_bytes(&mut self, addr: u64, data: &[u8]) -> Result<()> {
        let addr_usize = addr as usize;
        if addr_usize + data.len() >= self.size {
            bail!(
                "Memory write out of bounds: address 0x{:x} + data length {} > size 0x{:x}",
                addr_usize,
                data.len(),
                self.size
            );
        }

        self.data[addr_usize..addr_usize + data.len()].copy_from_slice(data);
        Ok(())
    }

    /// Resets all memory bytes to 0
    pub fn reset(&mut self) {
        self.data.fill(0);
    }

    /// Get the total size of memory in bytes
    pub fn size(&self) -> usize {
        self.size
    }

    /// Get raw access to memory (for debugging)
    pub fn dump(&self) -> &[u8] {
        &self.data
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new(1024 * 1024) // 1 MB default
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_memory() {
        let mem = Memory::new(1024);
        assert_eq!(mem.size(), 1024);
        assert_eq!(mem.dump().len(), 1024);
        // Verify all bytes are zero
        assert!(mem.dump().iter().all(|&b| b == 0));
    }

    #[test]
    #[should_panic(expected = "Memory size must be greater than 0")]
    fn test_new_memory_zero_size() {
        // Should panic when size is 0
        Memory::new(0);
    }

    #[test]
    fn test_read_write_u8() {
        let mut mem = Memory::new(1024);

        // Write and read back
        mem.write_u8(0, 0x42).unwrap();
        assert_eq!(mem.read_u8(0).unwrap(), 0x42);

        // Write at different address
        mem.write_u8(100, 0xFF).unwrap();
        assert_eq!(mem.read_u8(100).unwrap(), 0xFF);

        // Verify first write is unchanged
        assert_eq!(mem.read_u8(0).unwrap(), 0x42);
    }

    #[test]
    fn test_read_u8_out_of_bounds() {
        let mem = Memory::new(1024);
        assert!(mem.read_u8(1024).is_err());
        assert!(mem.read_u8(2000).is_err());
    }

    #[test]
    fn test_write_u8_out_of_bounds() {
        let mut mem = Memory::new(1024);
        assert!(mem.write_u8(1024, 0).is_err());
        assert!(mem.write_u8(2000, 0).is_err());
    }

    #[test]
    fn test_read_write_u16_little_endian() {
        let mut mem = Memory::new(1024);

        // Write 0x5678
        mem.write_u16(0x100, 0x5678).unwrap();

        // Verify little-endian byte order
        assert_eq!(mem.read_u8(0x100).unwrap(), 0x78); // LSB
        assert_eq!(mem.read_u8(0x101).unwrap(), 0x56); // MSB

        // Read back as u16
        assert_eq!(mem.read_u16(0x100).unwrap(), 0x5678);
    }

    #[test]
    fn test_u16_out_of_bounds() {
        let mut mem = Memory::new(1024);

        // At boundary (need 2 bytes)
        assert!(mem.write_u16(1023, 0).is_err());
        assert!(mem.read_u16(1023).is_err());

        // Beyond boundary
        assert!(mem.write_u16(1024, 0).is_err());
        assert!(mem.read_u16(1024).is_err());
    }

    #[test]
    fn test_read_write_u32_little_endian() {
        let mut mem = Memory::new(1024);

        // Write 0x12345678
        mem.write_u32(0x100, 0x12345678).unwrap();

        // Verify little-endian byte order
        assert_eq!(mem.read_u8(0x100).unwrap(), 0x78); // Byte 0 (LSB)
        assert_eq!(mem.read_u8(0x101).unwrap(), 0x56); // Byte 1
        assert_eq!(mem.read_u8(0x102).unwrap(), 0x34); // Byte 2
        assert_eq!(mem.read_u8(0x103).unwrap(), 0x12); // Byte 3 (MSB)

        // Read back as u32
        assert_eq!(mem.read_u32(0x100).unwrap(), 0x12345678);
    }

    #[test]
    fn test_u32_out_of_bounds() {
        let mut mem = Memory::new(1024);

        // Need 4 bytes
        assert!(mem.write_u32(1021, 0).is_err());
        assert!(mem.read_u32(1021).is_err());
    }

    #[test]
    fn test_read_write_u64_little_endian() {
        let mut mem = Memory::new(1024);

        // Write 0x123456789ABCDEF0
        mem.write_u64(0x100, 0x123456789ABCDEF0).unwrap();

        // Verify little-endian byte order
        assert_eq!(mem.read_u8(0x100).unwrap(), 0xF0); // Byte 0 (LSB)
        assert_eq!(mem.read_u8(0x101).unwrap(), 0xDE); // Byte 1
        assert_eq!(mem.read_u8(0x102).unwrap(), 0xBC); // Byte 2
        assert_eq!(mem.read_u8(0x103).unwrap(), 0x9A); // Byte 3
        assert_eq!(mem.read_u8(0x104).unwrap(), 0x78); // Byte 4
        assert_eq!(mem.read_u8(0x105).unwrap(), 0x56); // Byte 5
        assert_eq!(mem.read_u8(0x106).unwrap(), 0x34); // Byte 6
        assert_eq!(mem.read_u8(0x107).unwrap(), 0x12); // Byte 7 (MSB)

        // Read back as u64
        assert_eq!(mem.read_u64(0x100).unwrap(), 0x123456789ABCDEF0);
    }

    #[test]
    fn test_u64_out_of_bounds() {
        let mut mem = Memory::new(1024);

        // Need 8 bytes
        assert!(mem.write_u64(1017, 0).is_err());
        assert!(mem.read_u64(1017).is_err());
    }

    #[test]
    fn test_write_read_bytes() {
        let mut mem = Memory::new(1024);

        let data = vec![0x11, 0x22, 0x33, 0x44, 0x55];
        mem.write_bytes(0x100, &data).unwrap();

        let read_back = mem.read_bytes(0x100, 5).unwrap();
        assert_eq!(read_back, data);
    }

    #[test]
    fn test_bytes_out_of_bounds() {
        let mut mem = Memory::new(1024);
        let data = vec![0; 100];

        // Would overflow
        assert!(mem.write_bytes(1000, &data).is_err());
        assert!(mem.read_bytes(1000, 100).is_err());
    }

    #[test]
    fn test_reset() {
        let mut mem = Memory::new(1024);

        // Write some data
        mem.write_u32(0, 0xDEADBEEF).unwrap();
        mem.write_u32(100, 0xCAFEBABE).unwrap();

        // Reset
        mem.reset();

        // Verify all zero
        assert_eq!(mem.read_u32(0).unwrap(), 0);
        assert_eq!(mem.read_u32(100).unwrap(), 0);
        assert!(mem.dump().iter().all(|&b| b == 0));
    }

    #[test]
    fn test_memory_isolation() {
        let mut mem = Memory::new(1024);

        // Write to different addresses
        mem.write_u32(0, 0x11111111).unwrap();
        mem.write_u32(100, 0x22222222).unwrap();
        mem.write_u32(500, 0x33333333).unwrap();

        // Verify no interference
        assert_eq!(mem.read_u32(0).unwrap(), 0x11111111);
        assert_eq!(mem.read_u32(100).unwrap(), 0x22222222);
        assert_eq!(mem.read_u32(500).unwrap(), 0x33333333);
    }

    #[test]
    fn test_overlapping_writes() {
        let mut mem = Memory::new(1024);

        // Write u32 at 0
        mem.write_u32(0, 0x12345678).unwrap();

        // Partially overwrite with u16 at offset 2
        mem.write_u16(2, 0xABCD).unwrap();

        // Verify bytes
        assert_eq!(mem.read_u8(0).unwrap(), 0x78); // Unchanged
        assert_eq!(mem.read_u8(1).unwrap(), 0x56); // Unchanged
        assert_eq!(mem.read_u8(2).unwrap(), 0xCD); // Changed
        assert_eq!(mem.read_u8(3).unwrap(), 0xAB); // Changed
    }

    #[test]
    fn test_boundary_values() {
        let mut mem = Memory::new(1024);

        // Test with 0
        mem.write_u64(0, 0).unwrap();
        assert_eq!(mem.read_u64(0).unwrap(), 0);

        // Test with MAX
        mem.write_u64(0, u64::MAX).unwrap();
        assert_eq!(mem.read_u64(0).unwrap(), u64::MAX);

        // Test with mid-range
        mem.write_u64(0, 0x8000000000000000).unwrap();
        assert_eq!(mem.read_u64(0).unwrap(), 0x8000000000000000);
    }
}
