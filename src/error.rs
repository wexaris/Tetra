use crate::parse::SourceFile;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("invalid source file: {0}")]
    InvalidSource(SourceFile),

    #[error("{0}; {1}")]
    IOError(String, std::io::Error),

    #[error("compilation failed: {0}")]
    CompileError(String),

    #[error("compilation failed due to {0} error{}", if *(.0) > 1 { "s" } else { "" })]
    StageError(usize),
}
