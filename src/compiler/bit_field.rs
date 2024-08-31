use super::{CompileError, Integer};
use crate::architecture::BitPosition;

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
        let start = self.0.len() - (start + 1);
        let end = start + data.len();
        assert!(end <= self.0.len(), "{} <= {}", end, self.0.len());
        self.0.replace_range(start..end, data);
    }

    /// Replaces a range of bits in the bit field with the given bit ranges
    ///
    /// # Parameters
    ///
    /// * `start`: bit positions of the beginning of the ranges
    /// * `end`: bit positions of the end of the ranges
    /// * `data`: data to use as a replacement
    /// * `signed`: whether the data contains a signed or unsigned number
    ///
    /// # Errors
    ///
    /// Returns a `CompileError::ValueTooBig` if the data doesn't fit in the bit ranges
    pub fn replace(
        &mut self,
        start: &BitPosition,
        end: &BitPosition,
        data: i64,
        signed: bool,
    ) -> Result<(), CompileError> {
        let field_size = start.size(end);
        let data = Integer::build(data, field_size, None, Some(signed))?.to_string();
        let mut data = &data[data.len() - field_size..];
        match (start, end) {
            (BitPosition::Single(start), BitPosition::Single(_)) => {
                self.replace_range((*start).into(), data);
            }
            (BitPosition::Multiple(starts), BitPosition::Multiple(ends)) => {
                assert_eq!(
                    starts.len(),
                    ends.len(),
                    "Inconsistent instruction field location definition"
                );
                for (start, end) in starts.iter().zip(ends.iter()) {
                    let size = usize::from(start - end + 1);
                    self.replace_range((*start).into(), &data[..size]);
                    data = &data[size..];
                }
            }
            _ => panic!("Inconsistent instruction field location definition"),
        };
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
    use super::{BitField, BitPosition, CompileError};

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
        assert!(field
            .replace(
                &BitPosition::Single(15),
                &BitPosition::Single(12),
                0b1111,
                false,
            )
            .is_ok());
        assert_eq!(field.as_str(), "1111000000000000");
        assert!(field
            .replace(
                &BitPosition::Single(2),
                &BitPosition::Single(0),
                0b101,
                false,
            )
            .is_ok());
        assert_eq!(field.as_str(), "1111000000000101");
    }

    #[test]
    fn replace_separated() {
        let mut field = BitField::new(16);
        assert!(field
            .replace(
                &BitPosition::Multiple(vec![15, 7]),
                &BitPosition::Multiple(vec![12, 6]),
                0b10_0111,
                false,
            )
            .is_ok());
        assert_eq!(field.as_str(), "1001000011000000");
    }

    #[test]
    fn replace_error() {
        let mut field = BitField::new(16);
        assert_eq!(
            field.replace(
                &BitPosition::Single(15),
                &BitPosition::Single(12),
                18,
                false,
            ),
            Err(CompileError::IntegerTooBig(18, 0..16))
        );
        assert_eq!(
            field.replace(&BitPosition::Single(15), &BitPosition::Single(12), 8, true,),
            Err(CompileError::IntegerTooBig(8, -8..8))
        );
    }
}
