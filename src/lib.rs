#![doc(html_playground_url = "https://play.rust-lang.org")]

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Out of bound. Index: {}. Max index: {}", index, max_index)]
    OutOfBound { index: usize, max_index: usize },
}

/// Dynamicaly sized bitmap.
///
/// ```
/// # fn main() {
/// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
/// bitmap.set(0).unwrap();
/// bitmap.set(2).unwrap();
/// assert!(bitmap.get(0).unwrap());
/// assert!(!bitmap.get(1).unwrap());
/// assert!(bitmap.get(2).unwrap());
/// # }
/// ```
pub struct DynBitmap {
    buffer: Vec<u8>,
}

impl DynBitmap {
    /// Create new [bitmap](struct.DynBitmap.html) that is guaranteed to hold that many `bits`.
    ///
    /// # Example
    /// ```
    /// use dyn_bitmap::DynBitmap;
    /// # fn main() {
    /// let bimap = DynBitmap::contained(13);
    /// # }
    /// ```
    pub fn contained(bits: usize) -> Self {
        Self {
            buffer: vec![0u8; Self::bytes_required(bits)],
        }
    }

    /// Amount of bytes required for bitmap serialization.
    ///
    /// # Example
    /// ```
    /// use dyn_bitmap::DynBitmap;
    ///
    /// # fn main() {
    /// let bitmap = DynBitmap::contained(10);
    /// assert_eq!(bitmap.byte_size(), DynBitmap::bytes_required(10));
    /// # }
    /// ```
    pub const fn bytes_required(bits: usize) -> usize {
        (bits + 7) / 8
    }

    /// Index of contained bit byte.
    fn contained_byte_index(bit_index: usize) -> usize {
        bit_index / 8
    }

    /// Bit position in byte.
    const fn position_in_byte(bit_index: usize) -> u8 {
        (bit_index % 8) as u8
    }

    fn get_byte(&self, bit_index: usize) -> Result<u8, Error> {
        self.buffer
            .get(Self::contained_byte_index(bit_index))
            .copied()
            .ok_or(Error::OutOfBound {
                index: bit_index,
                max_index: self.bits_capacity(),
            })
    }

    fn get_byte_mut(&mut self, bit_index: usize) -> Result<&mut u8, Error> {
        let max_index = self.bits_capacity();
        self.buffer
            .get_mut(Self::contained_byte_index(bit_index))
            .ok_or(Error::OutOfBound {
                index: bit_index,
                max_index,
            })
    }

    /// Get bit value.
    ///
    /// # Example
    /// ```
    /// # fn main() {
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
    /// bitmap.set(0).unwrap();
    /// assert!(bitmap.get(0).unwrap());
    /// assert!(!bitmap.get(1).unwrap());
    /// # }
    /// ```
    pub fn get(&self, bit_index: usize) -> Result<bool, Error> {
        let byte: u8 = self.get_byte(bit_index)?;
        let position_in_byte = Self::position_in_byte(bit_index);
        let bit: u8 = (byte >> position_in_byte) & 0x01;
        Ok(bit == 1)
    }

    /// Set bit value as `true`.
    ///
    /// # Example
    /// ```
    /// # fn main() {
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
    /// assert!(!bitmap.get(0).unwrap());
    /// bitmap.set(0).unwrap();
    /// assert!(bitmap.get(0).unwrap());
    /// # }
    /// ```
    pub fn set(&mut self, bit_index: usize) -> Result<(), Error> {
        let byte = self.get_byte_mut(bit_index)?;
        let position_in_byte = Self::position_in_byte(bit_index);
        *byte |= 1 << position_in_byte;
        Ok(())
    }

    /// Set bit value as `false`.
    ///
    /// # Example
    /// ```
    /// # fn main() {
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
    /// bitmap.set(0).unwrap();
    /// assert!(bitmap.get(0).unwrap());
    /// bitmap.clear(0).unwrap();
    /// assert!(!bitmap.get(0).unwrap());
    /// # }
    /// ```
    pub fn clear(&mut self, bit_index: usize) -> Result<(), Error> {
        let byte = self.get_byte_mut(bit_index)?;
        let position_in_byte = Self::position_in_byte(bit_index) as u8;
        *byte &= !(1 << position_in_byte);
        Ok(())
    }

    /// Write [bitmap](struct.DynBitmap.html) by `impl std::io::Write`.
    ///
    /// # Example
    /// ```
    /// # fn main() {
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(8);
    ///
    /// bitmap.set(0).unwrap();
    /// bitmap.set(2).unwrap();
    /// bitmap.set(4).unwrap();
    /// bitmap.set(6).unwrap();
    ///
    /// let mut buffer: Vec<u8> = Default::default();
    /// let mut cursor = std::io::Cursor::new(&mut buffer);
    /// bitmap.write(cursor).unwrap();
    /// assert_eq!(&buffer, &0b0101_0101u8.to_le_bytes());
    /// }
    /// ```
    pub fn write<W: std::io::Write>(&self, mut writer: W) -> std::io::Result<()> {
        writer.write_all(&self.buffer)
    }

    /// Size of [bitmap](struct.DynBitmap.html) in bytes.
    ///
    /// # Example
    /// ```
    /// # fn main() {
    /// let bitmap = dyn_bitmap::DynBitmap::contained(9);
    /// assert_eq!(bitmap.byte_size(), 2);
    /// # }
    /// ```
    pub fn byte_size(&self) -> usize {
        self.buffer.len()
    }

    /// [Bitmap](struct.DynBitmap.html) bits capacity.
    ///
    /// # Example
    /// ```
    /// # fn main() {
    /// let bitmap = dyn_bitmap::DynBitmap::contained(9);
    /// assert_eq!(bitmap.bits_capacity(), 16);
    /// # }
    /// ```
    pub fn bits_capacity(&self) -> usize {
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
        assert_eq!(bitmap.bits_capacity(), 16);
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
        for idx in (0..bitmap.bits_capacity()).step_by(3) {
            bitmap.set(idx).unwrap();
        }

        let mut buffer = vec![0u8; bitmap.byte_size()];
        let cursor = std::io::Cursor::new(&mut buffer);

        bitmap.write(cursor).unwrap();
        assert_eq!(buffer.as_slice(), &0b1001_0010_0100_1001u16.to_ne_bytes());
    }

    #[test]
    fn value_write() {
        let mut bitmap = DynBitmap::contained(32);
        let mut cursor: std::io::Cursor<Vec<u8>> = Default::default();

        for i in 0 .. bitmap.bits_capacity()-1 {
            bitmap.set(i).unwrap();
            cursor.set_position(0);
            bitmap.write(&mut cursor).unwrap();

            assert_eq!(
                cursor.get_ref().as_slice(),
                ((1u32 << (i as u32 + 1)) - 1).to_ne_bytes().as_ref());
        }
    }

    #[test]
    fn value_get() {
        let mut bitmap = DynBitmap::contained(32);

        for i in 0 .. bitmap.bits_capacity()-1 {
            bitmap.set(i).unwrap();
        }

        for i in 0 .. bitmap.bits_capacity()-1 {
            assert!(bitmap.get(i).unwrap());
        }
    }

    #[test]
    fn value_clear() {
        let mut bitmap = DynBitmap::contained(32);

        for i in 0 .. bitmap.bits_capacity()-1 {
            bitmap.set(i).unwrap();
        }

        for i in 0 .. bitmap.bits_capacity()-1 {
            bitmap.clear(i).unwrap();
        }

        for i in 0 .. bitmap.bits_capacity()-1 {
            assert!(!bitmap.get(i).unwrap());
        }
    }
}
