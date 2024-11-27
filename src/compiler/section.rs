//! Module containing the definition of the memory sections

use super::ErrorKind;
use crate::architecture::NonEmptyRangeInclusiveU64;

/// Memory section manager
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    /// Address of the start of the section
    address: u64,
    /// Address of the end of the section
    end: u64,
    /// Name of the section
    name: &'static str,
}

impl Section {
    /// Creates a new [`Section`] with the given data
    ///
    /// # Parameters
    ///
    /// * `name`: name of the memory section
    /// * `bounds`: start/end addresses of the section
    pub const fn new(name: &'static str, bounds: &NonEmptyRangeInclusiveU64) -> Self {
        Self {
            name,
            address: bounds.start(),
            end: bounds.end(),
        }
    }

    /// Gets the first available address
    pub const fn get(&self) -> u64 {
        self.address
    }

    /// Reserves space for `size` addresses and returns the address of the beginning of the
    /// reserved space
    ///
    /// # Parameters
    ///
    /// * `size`: amount of addresses to reserve space for
    ///
    /// # Errors
    ///
    /// Returns a [`ErrorKind::MemorySectionFull`] if the there is not enough space in the section
    /// left for the requested allocation
    pub fn try_reserve(&mut self, size: u64) -> Result<u64, ErrorKind> {
        let res = self.address;
        self.address += size;
        if self.address - 1 > self.end {
            Err(ErrorKind::MemorySectionFull(self.name))
        } else {
            Ok(res)
        }
    }

    /// Aligns the first available address with the size given in bytes and returns the skipped
    /// region as `(start_addr, size)`. Size is guaranteed to be 0 if the address was already
    /// aligned
    ///
    /// # Parameters
    ///
    /// * `size`: size of the data values
    ///
    /// # Errors
    ///
    /// Returns a [`ErrorKind::MemorySectionFull`] if the there is not enough space in the section
    /// left for the requested alignment
    pub fn try_align(&mut self, align_size: u64) -> Result<(u64, u64), ErrorKind> {
        let offset = self.address % align_size;
        if offset == 0 {
            return Ok((self.address, 0));
        };
        let size = align_size - offset;
        let start = self.try_reserve(size)?;
        Ok((start, size))
    }

    /// Reserves space for `size` addresses and returns the address of the beginning of the
    /// reserved space, checking that the region is aligned with its size
    ///
    /// # Parameters
    ///
    /// * `size`: amount of addresses to reserve space for
    /// * `word_size`: size of a word in the architecture, in bytes
    ///
    /// # Errors
    ///
    /// Returns a [`ErrorKind::MemorySectionFull`] if the there is not enough space in the section
    /// left for the requested allocation, or a [`ErrorKind::DataUnaligned`] if the region isn't
    /// aligned
    pub fn try_reserve_aligned(&mut self, size: u64, word_size: u64) -> Result<u64, ErrorKind> {
        if self.address % size != 0 && self.address % word_size != 0 {
            return Err(ErrorKind::DataUnaligned {
                address: self.address,
                alignment: size,
                word_size,
            });
        }
        self.try_reserve(size)
    }
}

#[cfg(test)]
mod test {
    use super::{ErrorKind, NonEmptyRangeInclusiveU64, Section};

    fn range(start: u64, end: u64) -> NonEmptyRangeInclusiveU64 {
        NonEmptyRangeInclusiveU64::build(start, end).expect("This shouldn't fail")
    }

    #[test]
    fn reserve1() {
        let mut section = Section::new("test", &range(0, 3));
        assert_eq!(section.try_reserve(1), Ok(0));
        assert_eq!(section.try_reserve(1), Ok(1));
        assert_eq!(section.try_reserve(1), Ok(2));
        assert_eq!(section.try_reserve(1), Ok(3));
        assert_eq!(
            section.try_reserve(1),
            Err(ErrorKind::MemorySectionFull("test"))
        );
    }

    #[test]
    fn reserve4() {
        for i in 1..=4 {
            let mut section = Section::new("test2", &range(0, 11));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_reserve(4), Ok(i));
            assert_eq!(section.try_reserve(4), Ok(i + 4));
            assert_eq!(
                section.try_reserve(4),
                Err(ErrorKind::MemorySectionFull("test2"))
            );
        }
    }

    #[test]
    fn reserve6() {
        for i in 1..=6 {
            let mut section = Section::new("test3", &range(0, 17));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_reserve(6), Ok(i));
            assert_eq!(section.try_reserve(6), Ok(i + 6));
            assert_eq!(
                section.try_reserve(6),
                Err(ErrorKind::MemorySectionFull("test3"))
            );
        }
    }

    #[test]
    fn already_aligned() {
        let mut section = Section::new("test4", &range(0, 11));
        assert_eq!(section.try_align(4), Ok((0, 0)));
        assert_eq!(section.try_reserve(4), Ok(0));
        assert_eq!(section.get(), 4);
        assert_eq!(section.try_align(4), Ok((4, 0)));
        assert_eq!(section.get(), 4);
    }

    #[test]
    fn align_memory_limit() {
        for i in 1..4 {
            let mut section = Section::new("test5", &range(0, 3));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_align(4), Ok((i, 4 - i)));
        }
    }

    #[test]
    fn align_fail() {
        for i in 1..2 {
            let mut section = Section::new("test6", &range(0, 2));
            assert_eq!(section.try_align(4), Ok((0, 0)));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(
                section.try_align(4),
                Err(ErrorKind::MemorySectionFull("test6"))
            );
        }
    }

    #[test]
    fn align4() {
        for i in 1..4 {
            let mut section = Section::new("test7", &range(0, 11));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_align(4), Ok((i, 4 - i)));
            assert_eq!(section.get(), 4);
            assert_eq!(section.try_align(4), Ok((4, 0)));
        }
    }

    #[test]
    fn align6() {
        for i in 1..6 {
            let mut section = Section::new("test8", &range(0, 17));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_align(6), Ok((i, 6 - i)));
            assert_eq!(section.get(), 6);
            assert_eq!(section.try_align(6), Ok((6, 0)));
        }
    }

    #[test]
    fn try_reserve_aligned_ok() {
        let mut section = Section::new("test9", &range(0, 17));
        assert_eq!(section.try_reserve_aligned(2, 4), Ok(0));
        assert_eq!(section.try_reserve_aligned(2, 4), Ok(2));
        assert_eq!(section.try_reserve_aligned(8, 4), Ok(4));
        assert_eq!(section.try_reserve_aligned(3, 4), Ok(12));
        assert_eq!(section.try_reserve_aligned(3, 4), Ok(15));
    }

    #[test]
    fn try_reserve_aligned_fail() {
        let mut section = Section::new("test10", &range(0, 17));
        assert_eq!(section.try_reserve_aligned(1, 3), Ok(0));
        assert_eq!(
            section.try_reserve_aligned(2, 3),
            Err(ErrorKind::DataUnaligned {
                address: 1,
                alignment: 2,
                word_size: 3
            })
        );
    }
}
