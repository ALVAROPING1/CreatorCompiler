use super::error::Error as CompileError;

/// Memory section manager
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Section {
    address: u64,
    end: u64,
    name: &'static str,
}

impl Section {
    /// Constructs a new `Section` with the given data
    ///
    /// # Parameters
    ///
    /// * `name`: name of the memory section
    /// * `bounds`: start/end addresses of the section
    pub const fn new(name: &'static str, bounds: (u64, u64)) -> Self {
        Self {
            name,
            address: bounds.0,
            end: bounds.1 + 1,
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
    /// Returns a `CompileError::MemorySectionFull` if the there is not enough space in the section
    /// left for the requested allocation
    pub fn try_reserve(&mut self, size: u64) -> Result<u64, CompileError> {
        let res = self.address;
        self.address += size;
        if self.address > self.end {
            Err(CompileError::MemorySectionFull(self.name))
        } else {
            Ok(res)
        }
    }

    /// Aligns the first available address with the size given and returns the skipped region as
    /// `Some((start_addr, size))`. Returns `None` if the address was already aligned
    ///
    /// # Parameters
    ///
    /// * `size`: size of the data values
    ///
    /// # Errors
    ///
    /// Returns a `CompileError::MemorySectionFull` if the there is not enough space in the section
    /// left for the requested alignment
    pub fn try_align(&mut self, align_size: u64) -> Result<Option<(u64, u64)>, CompileError> {
        let offset = self.address % align_size;
        if offset == 0 {
            return Ok(None);
        };
        let size = align_size - offset;
        let start = self.try_reserve(size)?;
        Ok(Some((start, size)))
    }

    /// Reserves space for `size` addresses and returns the address of the beginning of the
    /// reserved space, checking that the region is aligned with its size
    ///
    /// # Parameters
    ///
    /// * `size`: amount of addresses to reserve space for
    ///
    /// # Errors
    ///
    /// Returns a `CompileError::MemorySectionFull` if the there is not enough space in the section
    /// left for the requested allocation, or a `CompileError::DataUnaligned` if the region isn't
    /// aligned
    pub fn try_reserve_aligned(&mut self, size: u64) -> Result<u64, CompileError> {
        if self.address % size != 0 {
            Err(CompileError::DataUnaligned {
                address: self.address,
                alignment: size,
            })
        } else {
            self.try_reserve(size)
        }
    }
}

#[cfg(test)]
mod test {
    use super::{CompileError, Section};

    #[test]
    fn reserve1() {
        let mut section = Section::new("test", (0, 3));
        assert_eq!(section.try_reserve(1), Ok(0));
        assert_eq!(section.try_reserve(1), Ok(1));
        assert_eq!(section.try_reserve(1), Ok(2));
        assert_eq!(section.try_reserve(1), Ok(3));
        assert_eq!(
            section.try_reserve(1),
            Err(CompileError::MemorySectionFull("test"))
        );
    }

    #[test]
    fn reserve4() {
        for i in 1..=4 {
            let mut section = Section::new("test2", (0, 11));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_reserve(4), Ok(i));
            assert_eq!(section.try_reserve(4), Ok(i + 4));
            assert_eq!(
                section.try_reserve(4),
                Err(CompileError::MemorySectionFull("test2"))
            );
        }
    }

    #[test]
    fn reserve6() {
        for i in 1..=6 {
            let mut section = Section::new("test3", (0, 17));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_reserve(6), Ok(i));
            assert_eq!(section.try_reserve(6), Ok(i + 6));
            assert_eq!(
                section.try_reserve(6),
                Err(CompileError::MemorySectionFull("test3"))
            );
        }
    }

    #[test]
    fn already_aligned() {
        let mut section = Section::new("test4", (0, 11));
        assert_eq!(section.try_align(4), Ok(None));
        assert_eq!(section.try_reserve(4), Ok(0));
        assert_eq!(section.get(), 4);
        assert_eq!(section.try_align(4), Ok(None));
        assert_eq!(section.get(), 4);
    }

    #[test]
    fn align_memory_limit() {
        for i in 1..4 {
            let mut section = Section::new("test5", (0, 3));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_align(4), Ok(Some((i, 4 - i))));
        }
    }

    #[test]
    fn align_fail() {
        for i in 1..2 {
            let mut section = Section::new("test6", (0, 2));
            assert_eq!(section.try_align(4), Ok(None));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(
                section.try_align(4),
                Err(CompileError::MemorySectionFull("test6"))
            );
        }
    }

    #[test]
    fn align4() {
        for i in 1..4 {
            let mut section = Section::new("test7", (0, 11));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_align(4), Ok(Some((i, 4 - i))));
            assert_eq!(section.get(), 4);
            assert_eq!(section.try_align(4), Ok(None));
        }
    }

    #[test]
    fn align6() {
        for i in 1..6 {
            let mut section = Section::new("test8", (0, 17));
            assert_eq!(section.try_reserve(i), Ok(0));
            assert_eq!(section.try_align(6), Ok(Some((i, 6 - i))));
            assert_eq!(section.get(), 6);
            assert_eq!(section.try_align(6), Ok(None));
        }
    }
}
