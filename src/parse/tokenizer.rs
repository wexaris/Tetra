use std::io::Read;
use crate::parse::{FilePos, SourceFile, Span, Token, TokenStream, TokenType, TokenError, TokenResult};

pub struct Tokenizer {
    source_file: SourceFile,
    source: Vec<u8>,
    byte_idx: usize,
    curr_byte: u8,
    next_byte: u8,
    curr_pos: FilePos,
    error_count: usize,
}

impl Tokenizer {
    pub fn new(source_file: SourceFile) -> crate::error::Result<Self> {
        let source = Self::read_file(&source_file)?;
        let tokenizer = Self {
            source_file,
            curr_pos: FilePos::initial(),
            curr_byte: source.get(0).cloned().unwrap_or(0), // Load initial bytes
            next_byte: source.get(1).cloned().unwrap_or(0), // Load initial bytes
            byte_idx: 2,                                                 // Pad for initial bytes
            source,
            error_count: 0,
        };

        Ok(tokenizer)
    }

    fn read_file(source: &SourceFile) -> crate::error::Result<Vec<u8>> {
        if !source.is_file() {
            return Err(crate::error::Error::InvalidSource(source.clone()));
        }

        let mut file = std::fs::File::open(source.as_path())
            .map_err(|e| crate::error::Error::IOError(format!("failed to open source file: {}", source.display()), e))?;

        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)
            .map_err(|e| crate::error::Error::IOError(format!("failed to read source file: {}", source.display()), e))?;

        Ok(buffer)
    }

    pub fn parse(&mut self) -> TokenStream {
        let tokens = self.map(|tok|
            tok.unwrap_or_else(|e| {
                println!("{e}");
                Token::invalid(e.get_span().span.clone())
            }))
            .collect::<Vec<_>>();

        TokenStream::from(self.source_file.clone(), tokens)
    }

    pub fn next_token(&mut self) -> TokenResult<Token> {
        while char::is_whitespace(self.curr_byte as char) {
            self.bump();
        }

        if self.curr_byte == b'/' {
            if self.next_byte == b'/' {
                while self.curr_byte != b'\r' && self.curr_byte != b'\n' && !self.is_eof() {
                    self.bump();
                }
            }
            else if self.next_byte == b'*' {
                self.bump();
                self.bump();
                while self.curr_byte != b'*' && self.next_byte != b'/' && !self.is_eof() {
                    self.bump();
                }
                self.bump();
                self.bump();
            }
            return self.next_token();
        }

        let start = self.curr_pos.clone();

        if self.is_eof() {
            return Ok(Token::eof(Span::new(start, 1)));
        }

        if Self::can_start_ident(self.curr_byte) {
            let mut ident_bytes = vec![];
            while Self::can_continue_ident(self.curr_byte) {
                ident_bytes.push(self.curr_byte);
                self.bump();
            }
            let span = self.span_from(start);

            let ident_str = match String::from_utf8(ident_bytes) {
                Ok(id) => id,
                Err(_) => {
                    return Err(TokenError::InvalidToken(span.with_file(&self.source_file)));
                }
            };

            if let Some(keyword) = self.match_keyword(&ident_str) {
                return Ok(Token::new(keyword, span));
            }

            return Ok(Token::new(TokenType::Id(ident_str.clone()), span));
        }

        if self.curr_byte.is_ascii_digit() {
            if self.curr_byte == b'0' && self.next_byte == b'x' { // hex
                self.bump();
                self.bump();

                if !self.curr_byte.is_ascii_hexdigit() {
                    let invalid_span = self.span_from(start).with_file(&self.source_file);
                    return Err(TokenError::InvalidNumber(invalid_span))
                }

                let mut num = 0f64;
                while self.curr_byte.is_ascii_hexdigit() {
                    num *= 16f64;
                    let digit = match self.curr_byte {
                        b'0'..=b'9' => self.curr_byte - b'0',
                        b'A'..=b'F' => self.curr_byte - b'A' + 10,
                        b'a'..=b'f' => self.curr_byte - b'a' + 10,
                        _ => unreachable!("invalid hex number"),
                    };
                    num += digit as f64;
                    self.bump()
                }

                return Ok(Token::new(TokenType::NumberVal(num), self.span_from(start)));
            }
            else if self.curr_byte == b'0' && self.next_byte == b'o' { // octal
                self.bump();
                self.bump();

                if !matches!(self.curr_byte, b'0'..=b'7') {
                    let invalid_span = self.span_from(start).with_file(&self.source_file);
                    return Err(TokenError::InvalidNumber(invalid_span))
                }

                let mut num = 0f64;
                while matches!(self.curr_byte, b'0'..=b'7') {
                    num *= 8f64;
                    num += (self.curr_byte - b'0') as f64;
                    self.bump()
                }

                return Ok(Token::new(TokenType::NumberVal(num), self.span_from(start)));
            }
            else if self.curr_byte == b'0' && self.next_byte == b'b' { // binary
                self.bump();
                self.bump();

                if !matches!(self.curr_byte, b'0' | b'1') {
                    let invalid_span = self.span_from(start).with_file(&self.source_file);
                    return Err(TokenError::InvalidNumber(invalid_span))
                }

                let mut num = 0f64;
                while matches!(self.curr_byte, b'0' | b'1') {
                    num *= 2f64;
                    num += (self.curr_byte - b'0') as f64;
                    self.bump()
                }

                return Ok(Token::new(TokenType::NumberVal(num), self.span_from(start)));
            }
            else {
                let mut num = 0f64;
                while self.curr_byte.is_ascii_digit() {
                    num *= 10f64;
                    num += (self.curr_byte - b'0') as f64;
                    self.bump()
                }

                if self.curr_byte == b'.' {
                    self.bump();

                    let mut pow = 0;
                    while self.curr_byte.is_ascii_digit() {
                        pow += 1;
                        let digit = (self.curr_byte - b'0') as f64;
                        let fraction = digit / 10f64.powi(pow);
                        num += fraction;
                        self.bump()
                    }
                }

                return Ok(Token::new(TokenType::NumberVal(num), self.span_from(start)));
            }
        }

        if let Some(ty) = self.match_symbol() {
            return Ok(Token::new(ty, self.span_from(start)));
        }

        self.bump();
        let invalid_span = self.span_from(start).with_file(&self.source_file);
        Err(TokenError::InvalidToken(invalid_span))
    }

    fn match_keyword(&self, raw: &str) -> Option<TokenType> {
        match raw {
            "var" => Some(TokenType::Var),
            "func" => Some(TokenType::Func),
            "struct" => Some(TokenType::Struct),
            "pub" => Some(TokenType::Pub),

            "if" => Some(TokenType::If),
            "else" => Some(TokenType::Else),
            "for" => Some(TokenType::For),
            "while" => Some(TokenType::While),
            "loop" => Some(TokenType::Loop),
            "continue" => Some(TokenType::Continue),
            "break" => Some(TokenType::Break),
            "return" => Some(TokenType::Return),

            "Number" => Some(TokenType::Number),
            "bool" => Some(TokenType::Bool),

            "true" => Some(TokenType::BoolVal(true)),
            "false" => Some(TokenType::BoolVal(false)),
            _ => None,
        }
    }

    fn match_symbol(&mut self) -> Option<TokenType> {
        match self.curr_byte {
            b'!' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::Neq)
                }
                else {
                    self.bump();
                    Some(TokenType::Not)
                }
            }
            b'=' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::Eq)
                }
                else {
                    self.bump();
                    Some(TokenType::Assign)
                }
            }
            b'<' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::LesserEq)
                }
                else {
                    self.bump();
                    Some(TokenType::Lesser)
                }
            }
            b'>' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::GreaterEq)
                }
                else {
                    self.bump();
                    Some(TokenType::Greater)
                }
            }
            b'&' if self.next_byte == b'&' => {
                self.bump();
                self.bump();
                Some(TokenType::LogicAnd)
            },
            b'&' if self.next_byte == b'=' => {
                self.bump();
                self.bump();
                Some(TokenType::AndAssign)
            },
            b'|' if self.next_byte == b'|' => {
                self.bump();
                self.bump();
                Some(TokenType::LogicOr)
            },
            b'|' if self.next_byte == b'=' => {
                self.bump();
                self.bump();
                Some(TokenType::OrAssign)
            },
            b'+' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::AddAssign)
                }
                else {
                    self.bump();
                    Some(TokenType::Plus)
                }
            }
            b'-' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::SubAssign)
                }
                else {
                    self.bump();
                    Some(TokenType::Minus)
                }
            }
            b'*' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::MulAssign)
                }
                else {
                    self.bump();
                    Some(TokenType::Star)
                }
            }
            b'/' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::DivAssign)
                }
                else {
                    self.bump();
                    Some(TokenType::Slash)
                }
            }
            b'%' => {
                if self.next_byte == b'=' {
                    self.bump();
                    self.bump();
                    Some(TokenType::ModAssign)
                }
                else {
                    self.bump();
                    Some(TokenType::Percent)
                }
            }

            b',' => {
                self.bump();
                Some(TokenType::Comma)
            },
            b'.' => {
                self.bump();
                Some(TokenType::Dot)
            },

            b':' => {
                if self.next_byte == b':' {
                    self.bump();
                    self.bump();
                    Some(TokenType::Scope)
                }
                else {
                    self.bump();
                    Some(TokenType::Colon)
                }
            },
            b';' => {
                self.bump();
                Some(TokenType::Semicolon)
            },

            b'(' => {
                self.bump();
                Some(TokenType::LParen)
            },
            b')' => {
                self.bump();
                Some(TokenType::RParen)
            },
            b'[' => {
                self.bump();
                Some(TokenType::LBracket)
            },
            b']' => {
                self.bump();
                Some(TokenType::RBracket)
            },
            b'{' => {
                self.bump();
                Some(TokenType::LBrace)
            },
            b'}' => {
                self.bump();
                Some(TokenType::RBrace)
            },
            _ => None,
        }
    }

    #[inline]
    fn can_start_ident(c: u8) -> bool {
        c.is_ascii_alphabetic() || c == b'_'
    }

    #[inline]
    fn can_continue_ident(c: u8) -> bool {
        c.is_ascii_alphanumeric() || c == b'_'
    }

    fn bump(&mut self) {
        if self.is_eof() {
            return;
        }

        // Update index position
        self.curr_pos.idx += 1;

        // Update line & col position
        if self.curr_byte == b'\n' || (self.curr_byte == b'\r' && self.next_byte != b'\n') {
            self.curr_pos.line += 1;
            self.curr_pos.col = 1;
        }
        else {
            self.curr_pos.col += 1;
        }

        // Move up next byte
        std::mem::swap(&mut self.curr_byte, &mut self.next_byte);
        self.next_byte = self.get_next_byte();
    }

    fn get_next_byte(&mut self) -> u8 {
        if self.byte_idx < self.source.len() {
            let byte = self.source[self.byte_idx];
            self.byte_idx += 1;
            byte
        }
        else { 0 }
    }

    #[inline]
    fn span_from(&self, start: FilePos) -> Span {
        let len = self.curr_pos.idx - start.idx;
        Span::new(start, len)
    }

    #[inline]
    fn is_eof(&self) -> bool { self.curr_pos.idx >= self.source.len() }

    #[inline]
    pub fn has_errors(&self) -> bool { self.error_count() != 0 }

    #[inline]
    pub fn error_count(&self) -> usize { self.error_count }
}

impl Iterator for Tokenizer {
    type Item = TokenResult<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            Ok(tok) if tok.is_eof() => None,
            other => Some(other)
        }
    }
}
