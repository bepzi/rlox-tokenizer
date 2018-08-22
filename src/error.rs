use std::error;
use std::fmt;

/// Represents an error that occurred while scanning Lox source code.
#[derive(Clone, Debug, PartialEq)]
pub struct TokenizerError {
    /// What line the error occurred on
    pub line: usize,
    /// What column the error occurred at
    pub col: usize,
    /// Additional contextual information
    pub msg: String,
}

impl fmt::Display for TokenizerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}:{}] Error: {}", self.line, self.col, self.msg)
    }
}

impl error::Error for TokenizerError {
    fn description(&self) -> &str {
        unimplemented!("this method is soft-deprecated; use std::fmt::Display instead");
    }

    fn cause(&self) -> Option<&dyn error::Error> {
        // NOTE: We could add a `cause` field to the struct to allow
        // for underlying `error::Error` causes
        None
    }
}
