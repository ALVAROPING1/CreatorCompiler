use super::ErrorKind;
use crate::architecture::IntegerType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Integer {
    value: u64,
    size: usize,
    r#type: Option<IntegerType>,
}

impl Integer {
    /// Creates a new `Integer`
    ///
    /// # Parameters
    ///
    /// * `value`: numeric value of the integer
    /// * `size`: size in bits of the integer
    /// * `r#type`: type of the integer
    /// * `signed`: If `Some`, strictly checks if value fits in the size given as signed/unsigned.
    ///   If `None`, casts the value to unsigned before checking
    ///
    /// # Errors
    ///
    /// Returns a `ErrorKind::ValueTooBig` if the value doesn't fit in the specified size
    pub fn build(
        value: i64,
        size: usize,
        r#type: Option<IntegerType>,
        signed: Option<bool>,
    ) -> Result<Self, ErrorKind> {
        let pow = |n: usize| 1 << n;
        let bounds = signed.map_or_else(
            || -pow(size - 1)..pow(size),
            |signed| {
                if signed {
                    let max = pow(size - 1);
                    -max..max
                } else {
                    0..pow(size)
                }
            },
        );
        if !bounds.contains(&value) {
            return Err(ErrorKind::IntegerTooBig(value, bounds));
        };
        #[allow(clippy::cast_sign_loss)]
        Ok(Self {
            value: value as u64 & ((1 << size) - 1),
            size,
            r#type,
        })
    }
}

impl std::fmt::Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.r#type {
            None => write!(f, "{:01$b}", self.value, self.size),
            Some(_) => write!(f, "{:01$X}", self.value, self.size / 4),
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod test {
    use super::{ErrorKind, Integer, IntegerType};

    #[test]
    fn bits_signed() {
        #[allow(clippy::cast_sign_loss)]
        for (x, x_str) in [(-8, "1000"), (-5, "1011"), (4, "0100"), (7, "0111")] {
            let val = Integer::build(x, 4, None, Some(true));
            assert_eq!(
                val,
                Ok(Integer {
                    value: x as u64 & 0xF,
                    size: 4,
                    r#type: None,
                })
            );
            assert_eq!(val.unwrap().to_string(), x_str);
        }
        for x in [8, -9] {
            assert_eq!(
                Integer::build(x, 4, None, Some(true)),
                Err(ErrorKind::IntegerTooBig(x, -8..8))
            );
        }
    }

    #[test]
    fn bits_unsigned() {
        #[allow(clippy::cast_sign_loss)]
        for (x, x_str) in [(0, "0000"), (4, "0100"), (15, "1111")] {
            let val = Integer::build(x, 4, None, Some(false));
            assert_eq!(
                val,
                Ok(Integer {
                    value: x as u64 & 0xF,
                    size: 4,
                    r#type: None,
                })
            );
            assert_eq!(val.unwrap().to_string(), x_str);
        }
        for x in [-1, 16] {
            assert_eq!(
                Integer::build(x, 4, None, Some(false)),
                Err(ErrorKind::IntegerTooBig(x, 0..16))
            );
        }
    }

    #[test]
    fn byte() {
        #[allow(clippy::cast_sign_loss)]
        for (x, x_str) in [(0, "0"), (4, "4"), (15, "F"), (-8, "8"), (-5, "B")] {
            let val = Integer::build(x, 4, Some(IntegerType::Byte), None);
            assert_eq!(
                val,
                Ok(Integer {
                    value: x as u64 & 0xF,
                    size: 4,
                    r#type: Some(IntegerType::Byte),
                })
            );
            assert_eq!(val.unwrap().to_string(), x_str);
        }
        for x in [-9, 16] {
            assert_eq!(
                Integer::build(x, 4, Some(IntegerType::Byte), None),
                Err(ErrorKind::IntegerTooBig(x, -8..16))
            );
        }
    }
}
