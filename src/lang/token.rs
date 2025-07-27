#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    Unary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerLiteralToken {
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentifierToken {
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    IntegerLiteral(IntegerLiteralToken),
    Identifier(IdentifierToken),
    EOF,
}

impl Token {
    pub fn get_class(&self) -> TokenClass {
        match self {
            Token::IntegerLiteral { .. } => TokenClass::Literal,
            Token::Identifier(id) => {
                if id.value.len() > 0
                    && id
                        .value
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_punctuation())
                {
                    TokenClass::Punctuation
                } else {
                    TokenClass::Identifier
                }
            }
            Token::EOF => TokenClass::EOF,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenClass {
    Literal,
    Identifier,
    Punctuation,
    EOF,
}

impl TokenClass {
    pub fn requires_spacing_left(self) -> bool {
        match self {
            TokenClass::Literal => true,
            TokenClass::Identifier => true,
            TokenClass::Punctuation => false,
            TokenClass::EOF => false,
        }
    }

    pub fn requires_spacing_right(self) -> bool {
        match self {
            TokenClass::Literal => true,
            TokenClass::Identifier => false,
            TokenClass::Punctuation => false,
            TokenClass::EOF => false,
        }
    }
}
