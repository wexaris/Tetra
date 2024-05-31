use crate::ast::Ident;
use crate::parse::FileSpan;
use crate::parse::token::{TokenType};

pub type TokenResult<T> = Result<T, TokenError>;

#[derive(thiserror::Error, Debug)]
pub enum TokenError {
    #[error("{0}: invalid token!")]
    InvalidToken(FileSpan),

    #[error("{0}: number has no valid digits!")]
    InvalidNumber(FileSpan),
}

impl TokenError {
    pub fn get_span(&self) -> &FileSpan {
        match self {
            TokenError::InvalidToken(span) => span,
            TokenError::InvalidNumber(span) => span,
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum ParseError {
    #[error("unexpected end of file!")]
    UnexpectedEof,

    #[error("unexpected token: '{}'{}", .tok, if .expected.is_empty() { "".to_string() } else { format!("; expected {}", .expected) } )]
    UnexpectedToken{ tok: TokenType, expected: String },

    #[error("statement should end with a semicolon!")]
    MissingSemi,

    #[error("dangling semicolon!")]
    DanglingSemi,

    #[error("invalid target of assignment!")]
    InvalidAssignExpression,

    #[error("invalid field access!")]
    InvalidFieldAccess,

    #[error("path name collision: {0}")]
    PathNameCollision(Ident),
}
