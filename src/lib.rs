pub mod architecture;
pub mod compiler;
#[cfg(feature = "js")]
pub mod js;
pub mod parser;

/// Trait representing an error that can be rendered for display
pub trait RenderError {
    /// Write the formatted error to a buffer. The written bytes should correspond to valid UTF-8
    ///
    /// # Parameters
    ///
    /// * `filename`: name of the file with the code
    /// * `src`: original source code parsed
    /// * `buffer`: writer in which to write the formatted error
    fn format(self, filename: &str, src: &str, buffer: &mut Vec<u8>)
    where
        Self: Sized;

    /// Render the error to a string
    ///
    /// # Parameters
    ///
    /// * `filename`: name of the file with the code
    /// * `src`: original source code parsed
    #[must_use]
    fn render(self, filename: &str, src: &str) -> String
    where
        Self: Sized,
    {
        let mut buffer = Vec::new();
        self.format(filename, src, &mut buffer);
        String::from_utf8(buffer).expect("the rendered error should be valid UTF-8")
    }
}

/// Builds a new lazily-initialized regex with a given literal string
///
/// # Panics
///
/// Panics if the literal string isn't a valid regex
macro_rules! build_regex {
    ($re:expr) => {
        Lazy::new(|| Regex::new($re).expect("All regexes should compile"))
    };
}
use build_regex as regex;
