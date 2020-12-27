#![doc(html_playground_url = "https://play.rust-lang.org")]

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Out of bound. Index: {}. Max index: {}", index, max_index)]
    OutOfBound { index: usize, max_index: usize },
}

/// Dynamicaly sized bitmap.
///
/// ```
/// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
/// bitmap.set(0, true).unwrap();
/// bitmap.set(2, true).unwrap();
/// assert!(bitmap.get(0).unwrap());
/// assert!(!bitmap.get(1).unwrap());
/// assert!(bitmap.get(2).unwrap());
/// ```
#[derive(Debug)]
pub struct DynBitmap {
    buffer: Vec<u8>,
}

impl DynBitmap {
    /// Create new [bitmap](struct.DynBitmap.html) that is guaranteed to hold that many `bits`.
    ///
    /// # Example
    /// ```
    /// use dyn_bitmap::DynBitmap;
    /// let bimap = DynBitmap::contained(13);
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
    /// let bitmap = DynBitmap::contained(10);
    /// assert_eq!(bitmap.byte_size(), DynBitmap::bytes_required(10));
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
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
    /// bitmap.set(0, true).unwrap();
    /// assert!(bitmap.get(0).unwrap());
    /// assert!(!bitmap.get(1).unwrap());
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
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(3);
    /// assert!(!bitmap.get(0).unwrap());
    /// bitmap.set(0, true).unwrap();
    /// assert!(bitmap.get(0).unwrap());
    /// ```
    pub fn set(&mut self, bit_index: usize, value: bool) -> Result<(), Error> {
        let byte: &mut u8 = self.get_byte_mut(bit_index)?;
        let position: u8 = Self::position_in_byte(bit_index);
        *byte = *byte & !(1 << position) | ((value as u8) << position);
        Ok(())
    }

    /// Write [bitmap](struct.DynBitmap.html) by `impl std::io::Write`.
    ///
    /// # Example
    /// ```
    /// let mut bitmap = dyn_bitmap::DynBitmap::contained(8);
    ///
    /// bitmap.set(0, true).unwrap();
    /// bitmap.set(2, true).unwrap();
    /// bitmap.set(4, true).unwrap();
    /// bitmap.set(6, true).unwrap();
    ///
    /// let mut buffer: Vec<u8> = Default::default();
    /// let mut cursor = std::io::Cursor::new(&mut buffer);
    /// bitmap.write(cursor).unwrap();
    /// assert_eq!(&buffer, &0b0101_0101u8.to_le_bytes());
    /// ```
    pub fn write<W: std::io::Write>(&self, mut writer: W) -> std::io::Result<()> {
        writer.write_all(&self.buffer)
    }

    /// Size of [bitmap](struct.DynBitmap.html) in bytes.
    ///
    /// # Example
    /// ```
    /// let bitmap = dyn_bitmap::DynBitmap::contained(9);
    /// assert_eq!(bitmap.byte_size(), 2);
    /// ```
    pub fn byte_size(&self) -> usize {
        self.buffer.len()
    }

    /// [Bitmap](struct.DynBitmap.html) bits capacity.
    ///
    /// # Example
    /// ```
    /// let bitmap = dyn_bitmap::DynBitmap::contained(9);
    /// assert_eq!(bitmap.bits_capacity(), 16);
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
        dbg!(&bitmap);

        assert_eq!(bitmap.byte_size(), 2);
        assert_eq!(bitmap.bits_capacity(), 16);
        assert_eq!(DynBitmap::bytes_required(12), 2);
    }

    #[test]
    fn get_byte() {
        let mut bitmap = DynBitmap::contained(16);
        dbg!(&bitmap);

        assert_eq!(
            bitmap.get_byte_mut(7).unwrap() as *const u8,
            bitmap.buffer.as_ptr(),
        );

        assert_eq!(bitmap.get_byte_mut(8).unwrap() as *const u8, unsafe {
            bitmap.buffer.as_ptr().add(1)
        },);
    }

    #[test]
    fn set_unset() {
        let mut bitmap = DynBitmap::contained(1);
        dbg!(&bitmap);

        assert!(!bitmap.get(0).unwrap());

        bitmap.set(0, true).unwrap();
        dbg!(&bitmap);
        assert!(bitmap.get(0).unwrap());

        bitmap.set(0, false).unwrap();
        dbg!(&bitmap);
        assert!(!bitmap.get(0).unwrap());
    }

    #[test]
    fn value_write() {
        let mut bitmap = DynBitmap::contained(32);
        let mut cursor: std::io::Cursor<Vec<u8>> = Default::default();

        for i in 0..bitmap.bits_capacity() - 1 {
            bitmap.set(i, true).unwrap();
            cursor.set_position(0);
            bitmap.write(&mut cursor).unwrap();

            assert_eq!(
                cursor.get_ref().as_slice(),
                ((1u32 << (i as u32 + 1)) - 1).to_le_bytes()
            );
        }
    }
}
