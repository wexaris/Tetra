use std::fmt::Formatter;
use crate::parse::{SourceFile, Span};

pub struct TokenStream {
    pub source: SourceFile,
    pub tokens: Vec<Token>,
    idx: usize,
}

impl TokenStream {
    #[inline]
    pub fn new(source: SourceFile, tokens: Vec<Token>) -> Self {
        Self { source, tokens, idx: 0 }
    }

    pub fn from(source: SourceFile, mut tokens: Vec<Token>) -> Self {
        // Check if last token is EOF
        let last = tokens.last();
        let last_is_eof = last.map_or(false, |tok| tok.is_eof());

        // If last token isn't EOF, append it
        if !last_is_eof {
            let pos = last.map_or_else(
                || Span::initial(),
                |tok| tok.span.next_char());
            tokens.push(Token::eof(pos));
        }

        TokenStream::new(source, tokens)
    }
    
    pub fn next(&mut self) -> Option<&Token> {
        if self.idx < self.tokens.len() {
            let token = self.tokens.get(self.idx);
            self.idx += 1;
            token
        }
        else {
            self.tokens.last()
        }
    }

    #[inline]
    pub fn curr(&self) -> Option<&Token> {
        self.tokens.get(self.idx)
    }
    
    #[inline]
    pub fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.idx + 1)
    }

    #[inline]
    pub fn is_eof(&self) -> bool {
        self.idx >= self.tokens.len()
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub ty: TokenType,
    pub span: Span,
}

impl Token {
    pub fn new(ty: TokenType, span: Span) -> Self {
        Token { ty, span }
    }

    pub const fn eof(span: Span) -> Self {
        Token { ty: TokenType::Eof, span, }
    }

    pub const fn invalid(span: Span) -> Self {
        Token { ty: TokenType::Invalid, span, }
    }

    pub fn is_eof(&self) -> bool { self.ty.is_eof() }
    pub fn is_valid(&self) -> bool { self.ty.is_valid() }
    pub fn is_unary_op(&self) -> bool { self.ty.is_unary_op() }
    pub fn is_binary_op(&self) -> bool { self.ty.is_binary_op() }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} [{}]", self.ty, self.span)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    Id(String),

    // Keywords
    Var,
    Func,
    Struct,
    Pub,
    
    If,
    Else,
    For,
    While,
    Loop,
    Continue,
    Break,
    Return,
    
    // Types
    Number,
    Bool,

    // Values
    NumberVal(f64),
    BoolVal(bool),
    
    // Symbols
    Eq, Neq,
    Lesser, LesserEq,
    Greater, GreaterEq,
    LogicAnd, LogicOr,

    Not,
    Plus, Minus,
    Star, Slash, Percent,

    Assign,
    AndAssign, OrAssign,
    AddAssign, SubAssign,
    MulAssign, DivAssign, ModAssign,

    Scope,
    Dot, Comma,
    Colon, Semicolon,
    LParen, RParen,
    LBrace, RBrace,
    LBracket, RBracket,

    // Special
    Eof,
    Invalid,
}

impl TokenType {
    #[inline]
    pub fn is_eof(&self) -> bool { *self == TokenType::Eof }
    
    #[inline]
    pub fn is_valid(&self) -> bool { *self != TokenType::Invalid }

    #[inline]
    pub fn is_unary_op(&self) -> bool {
        matches!(*self, TokenType::Not | TokenType::Plus | TokenType::Minus)
    }

    #[inline]
    pub fn is_binary_op(&self) -> bool {
        matches!(*self,
            TokenType::Dot  |
            TokenType::Star | TokenType::Slash | TokenType::Percent |
            TokenType::Plus | TokenType::Minus |
            TokenType::Eq   | TokenType::Neq   |
            TokenType::Lesser   | TokenType::LesserEq  |
            TokenType::Greater  | TokenType::GreaterEq |
            TokenType::LogicAnd | TokenType::LogicOr |
            TokenType::Assign |
            TokenType::AndAssign | TokenType::OrAssign |
            TokenType::AddAssign | TokenType::SubAssign |
            TokenType::MulAssign | TokenType::DivAssign | TokenType::ModAssign
        )
    }

    #[inline]
    pub fn is_assign(&self) -> bool {
        matches!(*self,
            TokenType::Assign |
            TokenType::AndAssign | TokenType::OrAssign |
            TokenType::AddAssign | TokenType::SubAssign |
            TokenType::MulAssign | TokenType::DivAssign | TokenType::ModAssign)
    }

    #[inline]
    pub fn assign_pre_op(&self) -> Option<TokenType> {
        match self {
            TokenType::AndAssign => Some(TokenType::LogicAnd),
            TokenType::OrAssign => Some(TokenType::LogicOr),
            TokenType::AddAssign => Some(TokenType::Plus),
            TokenType::SubAssign => Some(TokenType::Minus),
            TokenType::MulAssign => Some(TokenType::Star),
            TokenType::DivAssign => Some(TokenType::Slash),
            TokenType::ModAssign => Some(TokenType::Percent),
            _ => None,
        }
    }
}

impl std::fmt::Display for TokenType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenType::Id(name) => write!(f, "Ident ({name})"),
            TokenType::NumberVal(val) => write!(f, "Number ({val})"),
            TokenType::BoolVal(val) => write!(f, "Bool ({val})"),
            other => write!(f, "{:?}", other),
        }
    }
}
