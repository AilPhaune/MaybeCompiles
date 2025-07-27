use crate::lang::{
    source::SourceFile,
    token::{IdentifierToken, IntegerLiteralToken, Token, TokenClass},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LexerPosition {
    offset: usize,
    nchar: usize,
    line: usize,
    column: usize,
}

impl LexerPosition {
    pub const fn new() -> LexerPosition {
        LexerPosition {
            offset: 0,
            nchar: 0,
            line: 1,
            column: 1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexerState {
    position: LexerPosition,
    last_class: Option<TokenClass>,
}

pub struct Lexer {
    source: SourceFile,

    position: LexerPosition,
    last_class: Option<TokenClass>,
}

impl Lexer {
    pub fn new(source: SourceFile) -> Lexer {
        Lexer {
            source,
            position: LexerPosition::new(),
            last_class: None,
        }
    }

    /// Get the current state
    pub fn push(&self) -> LexerState {
        LexerState {
            position: self.position,
            last_class: self.last_class,
        }
    }

    /// Sets the current state
    pub fn pop(&mut self, position: LexerState) {
        self.position = position.position;
        self.last_class = position.last_class;
    }

    /// Gets a substring of the source file
    fn get_substr(&self, offset: usize, len: usize) -> Option<&str> {
        self.source.get_contents().get(offset..(offset + len))
    }

    /// Peek the remaining characters
    fn peek_remaining(&self) -> Option<&str> {
        self.source.get_contents().get(self.position.offset..)
    }

    /// Peek the next character
    fn peek(&self) -> Option<char> {
        self.peek_remaining().and_then(|s| s.chars().next())
    }

    /// Advance the lexer
    fn advance(&mut self, value: char) {
        self.position.offset += value.len_utf8();
        if value == '\n' {
            self.position.line += 1;
            self.position.column = 1;
        } else {
            self.position.column += 1;
        }
        self.position.nchar += 1;
    }

    /// Consumes a character if it matches the predicate
    fn consume(&mut self, predicate: impl Fn(char) -> bool) -> Option<char> {
        self.peek().and_then(|c| {
            if predicate(c) {
                self.advance(c);
                Some(c)
            } else {
                None
            }
        })
    }

    /// Skips a whitespace
    fn skip_whitespace(&mut self) -> bool {
        self.consume(|c| c.is_whitespace()).is_some()
    }

    /// Skips multiple whitespaces
    fn skip_whitespaces(&mut self) -> usize {
        let mut count = 0;
        while self.skip_whitespace() {
            count += 1;
        }
        count
    }

    /// Parse an integer literal
    fn make_integer_literal(&mut self) -> Option<Token> {
        let begin_pos = self.push();
        let mut len = 0;
        let mut first_char = '\0';
        while let Some(c) = self.peek() {
            if len == 0 {
                if c.is_ascii_digit() {
                    len += 1;
                    first_char = c;
                    self.advance(c);
                } else {
                    break;
                }
            } else {
                match c {
                    '0'..='9' => {
                        if first_char == '0' {
                            break;
                        }
                        len += 1;
                        self.advance(c);
                    }
                    '_' => {
                        if first_char == '0' {
                            break;
                        }
                        len += 1;
                        self.advance(c);
                    }
                    _ => break,
                }
            }
        }

        if len == 0 {
            self.pop(begin_pos);
            None
        } else {
            self.last_class = Some(TokenClass::Literal);

            Some(Token::IntegerLiteral(IntegerLiteralToken {
                value: self.get_substr(begin_pos.position.offset, len)?.to_string(),
            }))
        }
    }

    fn make_identifier(&mut self) -> Option<Token> {
        let begin_pos = self.push();
        let mut len = 0;
        while let Some(c) = self.peek() {
            if len == 0 {
                if c.is_alphabetic() {
                    len += 1;
                    self.advance(c);
                } else if c.is_ascii_punctuation() {
                    len += 1;
                    self.advance(c);
                    break;
                } else {
                    break;
                }
            } else {
                if !c.is_whitespace() && !c.is_ascii_punctuation() {
                    len += 1;
                    self.advance(c);
                } else {
                    break;
                }
            }
        }

        if len == 0 {
            None
        } else {
            self.last_class = Some(TokenClass::Identifier);
            Some(Token::Identifier(IdentifierToken {
                value: self.get_substr(begin_pos.position.offset, len)?.to_string(),
            }))
        }
    }

    fn make_token(&mut self) -> Option<Token> {
        if self.position.offset >= self.source.get_byte_len() {
            self.last_class = Some(TokenClass::EOF);
            return Some(Token::EOF);
        }

        if let Some(token) = self.make_integer_literal() {
            return Some(token);
        }

        if let Some(token) = self.make_identifier() {
            return Some(token);
        }

        None
    }

    pub fn next_token(&mut self) -> Option<Token> {
        if self.last_class == Some(TokenClass::EOF) {
            return None;
        }

        let whitespaces = self.skip_whitespaces();
        let last_class = self.last_class;
        let token = self.make_token()?;
        if whitespaces == 0
            && token.get_class().requires_spacing_left()
            && last_class
                .map(TokenClass::requires_spacing_right)
                .unwrap_or(false)
        {
            None
        } else {
            Some(token)
        }
    }
}

impl Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}
