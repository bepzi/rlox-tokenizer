#[derive(Copy, Clone, Debug, PartialEq)]
/// Represents a piece of Lox syntax created from Lox source code.
pub struct Token<'a> {
    /// What kind of `Token` this is
    pub token_type: TokenType,
    /// The piece of the source code this `Token` comes from
    pub lexeme: &'a str,
    /// The grapheme offset in the source code where the lexeme starts
    ///
    /// (Can be used to calculate the line and column number)
    pub offset: usize,
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[allow(missing_docs)]
/// Describes what kind of syntax token a lexeme represents.
pub enum TokenType {
    // Only 1-character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // 1 or maybe 2-character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    Identifier,
    String,
    Number,

    // Keywords
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}
