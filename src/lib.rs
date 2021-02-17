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
    bit_count: usize,
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
            bit_count: bits,
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
                max_index: self.arity(),
            })
    }

    fn get_byte_mut(&mut self, bit_index: usize) -> Result<&mut u8, Error> {
        let max_index = self.arity();
        self.buffer
            .get_mut(Self::contained_byte_index(bit_index))
            .ok_or(Error::OutOfBound {
                index: bit_index,
                max_index,
            })
    }

    /// Get `value` from `byte` for exact bit-`index`.
    #[inline(always)]
    fn get_value(byte: u8, index: u8) -> bool {
        // We shift byte-value on `index`-bit and apply bit **and**-operation
        // with `0b0000_0001`.
        ((byte >> index) & 0b0000_0001) == 1
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
        if bit_index >= self.bit_count {
            return Err(Error::OutOfBound {
                index: bit_index,
                max_index: self.bit_count - 1,
            });
        }

        let byte: u8 = self.get_byte(bit_index)?;
        let position_in_byte = Self::position_in_byte(bit_index);
        Ok(Self::get_value(byte, position_in_byte))
    }

    /// Set `value` in `byte` for exact bit-`index`.
    #[inline(always)]
    fn set_value(byte: u8, value: bool, index: u8) -> u8 {
        // Unset `index` bit and set value.
        byte & !(1 << index) | ((value as u8) << index)
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
        *byte = Self::set_value(*byte, value, position);
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
    /// assert_eq!(bitmap.arity(), 9);
    /// ```
    pub fn arity(&self) -> usize {
        self.bit_count
    }

    /// Iterate over the bitmap.
    ///
    /// # Example
    /// ```
    /// use dyn_bitmap::DynBitmap;
    ///
    /// let bitmap: DynBitmap = std::iter::repeat(true).take(128).collect();
    /// let all: bool = bitmap.iter().all(|b| b);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = bool> + '_ {
        self.buffer
            .iter()
            .flat_map(|&byte| (0..=7).map(move |idx| Self::get_value(byte, idx)))
            .take(self.arity())
    }
}

impl std::iter::FromIterator<bool> for DynBitmap {
    fn from_iter<I: IntoIterator<Item = bool>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let initial_size = iter.size_hint().1.map(Self::bytes_required).unwrap_or(0);

        let mut buffer = Vec::with_capacity(initial_size);
        let mut bit_idx: u8 = 0;
        let mut byte: u8 = 0;
        let mut bit_count = 0;

        for value in iter {
            if bit_idx == 8 {
                buffer.push(byte);
                byte = 0;
                bit_idx = 0;
            }

            byte = DynBitmap::set_value(byte, value, bit_idx);
            bit_idx += 1;
            bit_count += 1;
        }

        buffer.push(byte);

        Self { buffer, bit_count }
    }
}

#[cfg(test)]
mod bitmap_tests {
    use super::{DynBitmap, Error};

    #[test]
    fn new() {
        let bitmap = DynBitmap::contained(12);
        dbg!(&bitmap);

        assert_eq!(bitmap.byte_size(), 2);
        assert_eq!(bitmap.arity(), 12);
        assert_eq!(DynBitmap::bytes_required(12), 2);
    }

    #[test]
    fn set_value() {
        assert_eq!(DynBitmap::set_value(0b1010_1010, true, 2), 0b1010_1110);
        assert_eq!(DynBitmap::set_value(0b1010_1010, false, 1), 0b1010_1000);
    }

    #[test]
    fn get_byte() {
        let mut bitmap = DynBitmap::contained(150);
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
    fn get() {
        let mut bitmap = DynBitmap::contained(7);
        dbg!(&bitmap);

        bitmap.set(6, true).unwrap();
        dbg!(&bitmap);

        assert!(bitmap.get(6).unwrap());

        match bitmap.get(9) {
            Ok(_) => unreachable!("This brunch must fail!"),
            Err(Error::OutOfBound { index, max_index }) => {
                assert_eq!(index, 9);
                assert_eq!(max_index, 6);
            }
        };
    }

    #[test]
    fn iter() {
        let source = [true, false, false].iter().cycle().take(140);
        let from_iter: DynBitmap = source.clone().copied().collect();
        assert_eq!(from_iter.iter().size_hint().1.unwrap(), 140);

        let source: Vec<_> = source.copied().collect();
        let from_iter: Vec<_> = from_iter.iter().collect();
        assert_eq!(source, from_iter);
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
    fn from_iter() {
        let source = &[true, false, false].iter().cycle().take(10);
        let from_iter: DynBitmap = source.clone().cloned().collect();

        let mut manual = DynBitmap::contained(10);
        for (idx, &value) in source.clone().enumerate() {
            manual.set(idx, value).unwrap();
        }

        assert_eq!(from_iter.buffer, manual.buffer);
        assert_eq!(from_iter.bit_count, manual.bit_count);
    }

    #[test]
    fn value_write() {
        let mut bitmap = DynBitmap::contained(32);
        let mut cursor: std::io::Cursor<Vec<u8>> = Default::default();

        for i in 0..bitmap.arity() - 1 {
            bitmap.set(i, true).unwrap();
            cursor.set_position(0);
            bitmap.write(&mut cursor).unwrap();

            assert_eq!(
                cursor.get_ref().as_slice(),
                ((1u32 << (i as u32 + 1)) - 1).to_le_bytes()
            );
        }
    }

    #[test]
    fn small_values_from_iter_test() {
        let from_iter: DynBitmap = [true, false].iter().cycle().take(3).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b101);
        assert_eq!(from_iter.buffer.len(), 1);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(4).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b0101);
        assert_eq!(from_iter.buffer.len(), 1);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(5).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b10101);
        assert_eq!(from_iter.buffer.len(), 1);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(6).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b010101);
        assert_eq!(from_iter.buffer.len(), 1);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(7).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b1010101);
        assert_eq!(from_iter.buffer.len(), 1);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(8).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b01010101);
        assert_eq!(from_iter.buffer.len(), 1);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(9).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b01010101);
        assert_eq!(from_iter.buffer[1], 0b1);
        assert_eq!(from_iter.buffer.len(), 2);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(10).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b01010101);
        assert_eq!(from_iter.buffer[1], 0b01);
        assert_eq!(from_iter.buffer.len(), 2);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(11).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b01010101);
        assert_eq!(from_iter.buffer[1], 0b101);
        assert_eq!(from_iter.buffer.len(), 2);

        let from_iter: DynBitmap = [true, false].iter().cycle().take(16).copied().collect();
        assert_eq!(from_iter.buffer[0], 0b01010101);
        assert_eq!(from_iter.buffer[1], 0b01010101);
        assert_eq!(from_iter.buffer.len(), 2);
    }
}
