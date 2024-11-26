//! Module containing the definition of the spans used to track regions of the assembly source code
//! throughout the crate

/// Range of characters in the source code of an element
pub type Span = std::ops::Range<usize>;
/// Value with an attached `Span`
pub type Spanned<T> = (T, Span);
