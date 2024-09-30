use super::{ErrorKind, Integer};
use crate::architecture::BitRange;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitField(String);

impl BitField {
    /// Constructs a new bit field with the given size
    ///
    /// # Parameters
    ///
    /// * `size`: size of the bit field
    #[must_use]
    pub fn new(size: usize) -> Self {
        Self("0".repeat(size))
    }

    /// Replaces a range of bits in the bit field
    ///
    /// # Parameters
    ///
    /// * `start`: starting bit of the range
    /// * `data`: binary string of bits to use as a replacement
    fn replace_range(&mut self, start: usize, data: &str) {
        let end = self.0.len() - start;
        let start = end - data.len();
        assert!(end <= self.0.len(), "{} <= {}", end, self.0.len());
        self.0.replace_range(start..end, data);
    }

    /// Replaces a range of bits in the bit field with the given values
    ///
    /// # Parameters
    ///
    /// * `range`: ranges of bits to replace
    /// * `data`: data to use as a replacement
    /// * `signed`: whether the data contains a signed or unsigned number
    ///
    /// # Errors
    ///
    /// Returns a `ErrorKind::ValueTooBig` if the data doesn't fit in the bit ranges
    pub fn replace(&mut self, range: &BitRange, data: i64, signed: bool) -> Result<(), ErrorKind> {
        let field_size = range.size();
        let data = Integer::build(data, field_size, None, Some(signed))?.to_string();
        let mut data = &data[data.len() - field_size..];
        for segment in range.iter() {
            let size = segment.size().get().into();
            self.replace_range(segment.start().into(), &data[..size]);
            data = &data[size..];
        }
        assert_eq!(data.len(), 0, "(data.len() == {}) != 0", data.len());
        Ok(())
    }

    /// Extracts a string slice containing the entire `BitField`
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

#[cfg(test)]
mod test {
    use crate::architecture::NonEmptyRangeInclusiveU8;

    use super::{BitField, BitRange, ErrorKind};

    fn range(segments: Vec<(u8, u8)>) -> BitRange {
        BitRange::build(
            segments
                .into_iter()
                .map(|(a, b)| NonEmptyRangeInclusiveU8::build(b, a).expect("This shouldn't fail"))
                .collect(),
        )
        .expect("this shouldn't fail")
    }

    #[test]
    fn new() {
        assert_eq!(
            BitField::new(32).as_str(),
            "00000000000000000000000000000000"
        );
        assert_eq!(BitField::new(8).as_str(), "00000000");
    }

    #[test]
    fn replace_contiguous() {
        let mut field = BitField::new(16);
        assert!(field.replace(&range(vec![(15, 12)]), 0b1111, false).is_ok());
        assert_eq!(field.as_str(), "1111000000000000");
        assert!(field.replace(&range(vec![(2, 0)]), 0b101, false,).is_ok());
        assert_eq!(field.as_str(), "1111000000000101");
    }

    #[test]
    fn replace_separated() {
        let mut field = BitField::new(16);
        assert!(field
            .replace(&range(vec![(15, 12), (7, 6)]), 0b10_0111, false,)
            .is_ok());
        assert_eq!(field.as_str(), "1001000011000000");
    }

    #[test]
    fn replace_error() {
        let mut field = BitField::new(16);
        assert_eq!(
            field.replace(&range(vec![(15, 12)]), 18, false,),
            Err(ErrorKind::IntegerTooBig(18, 0..16))
        );
        assert_eq!(
            field.replace(&range(vec![(15, 12)]), 8, true),
            Err(ErrorKind::IntegerTooBig(8, -8..8))
        );
    }
}
