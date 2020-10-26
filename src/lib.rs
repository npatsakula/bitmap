#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Out of bound. Index: {}. Max index: {}", index, max_index)]
    OutOfBound { index: usize, max_index: usize },
}

pub struct DynBitmap {
    buffer: Vec<u8>,
}

impl DynBitmap {
    /// Create new `Self` that is guaranteed to hold that many `bits`.
    pub fn contained(bits: usize) -> Self {
        Self {
            buffer: vec![0u8; Self::bytes_required(bits)],
        }
    }

    /// Amount of bytes required for bitmap serialization.
    pub const fn bytes_required(bits: usize) -> usize {
        (bits + 7) / 8
    }

    /// Index of contained bit byte.
    fn contained_byte_index(bit_index: usize) -> usize {
        bit_index / 8
    }

    /// Bit position in byte.
    const fn position_in_byte(bit: usize) -> u8 {
        (bit % 8) as u8
    }

    fn get_byte(&self, bit: usize) -> Result<u8, Error> {
        self.buffer
            .get(Self::contained_byte_index(bit))
            .copied()
            .ok_or(Error::OutOfBound {
                index: bit,
                max_index: self.bits(),
            })
    }

    fn get_byte_mut(&mut self, bit: usize) -> Option<&mut u8> {
        self.buffer.get_mut(Self::contained_byte_index(bit))
    }

    pub fn get(&self, bit: usize) -> Result<bool, Error> {
        let byte: u8 = self.get_byte(bit)?;
        let position_in_byte = Self::position_in_byte(bit);
        let bit: u8 = (byte >> position_in_byte) & 0x01;
        Ok(bit == 1)
    }

    pub fn set(&mut self, bit: usize) -> Option<()> {
        let byte = self.get_byte_mut(bit)?;
        let position_in_byte = Self::position_in_byte(bit) as u8;
        *byte |= 1 << position_in_byte;
        Some(())
    }

    pub fn clear(&mut self, bit: usize) -> Option<()> {
        let byte = self.get_byte_mut(bit)?;
        let position_in_byte = Self::position_in_byte(bit) as u8;
        *byte &= !(1 << position_in_byte);
        Some(())
    }

    pub fn write<W: std::io::Write>(&self, mut writer: W) -> std::io::Result<()> {
        writer.write_all(&self.buffer)
    }

    /// Size of bitmap in bytes.
    pub fn byte_size(&self) -> usize {
        self.buffer.len()
    }

    pub fn bits(&self) -> usize {
        self.byte_size() * 8
    }
}

#[cfg(test)]
mod bitmap_tests {
    use super::DynBitmap;

    #[test]
    fn new() {
        let bitmap = DynBitmap::contained(12);
        assert_eq!(bitmap.byte_size(), 2);
        assert_eq!(bitmap.bits(), 16);
        assert_eq!(DynBitmap::bytes_required(12), 2);
    }

    #[test]
    fn set_clear() {
        let mut bitmap = DynBitmap::contained(12);

        assert!(!bitmap.get(6).unwrap());
        bitmap.set(6).unwrap();
        assert!(bitmap.get(6).unwrap());

        bitmap.clear(6).unwrap();
        assert!(!bitmap.get(6).unwrap());

        assert!(!bitmap.get(0).unwrap());
        assert!(!bitmap.get(11).unwrap());
        bitmap.set(0).unwrap();
        bitmap.set(11).unwrap();
        assert!(bitmap.get(0).unwrap());
        assert!(bitmap.get(11).unwrap());

        assert!(bitmap.get(17).is_err())
    }

    #[test]
    fn write() {
        let mut bitmap = DynBitmap::contained(12);
        for idx in (0..bitmap.bits()).step_by(3) {
            bitmap.set(idx).unwrap();
        }

        let mut buffer = vec![0u8; bitmap.byte_size()];
        let cursor = std::io::Cursor::new(&mut buffer);

        bitmap.write(cursor).unwrap();
        assert_eq!(buffer.as_slice(), &0b1001_0010_0100_1001u16.to_ne_bytes());
    }
}
