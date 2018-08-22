#![warn(bad_style)]
#![warn(future_incompatible)]
#![warn(nonstandard_style)]
#![warn(rust_2018_compatibility)]
#![warn(rust_2018_idioms)]
#![warn(missing_docs)]

//! Tokenizes Bob Nystrom's
//! [Lox](https://github.com/munificent/craftinginterpreters)
//! programming language, from [Crafting
//! Interpreters](https://craftinginterpreters.com/).
//!
//! This crate provides the initial transformation from Lox source
//! code to syntax tokens. It is based off of the reference [C
//! implementation](https://github.com/munificent/craftinginterpreters/tree/master/c),
//! but with Rust idioms.
//!
//! # Implementation Differences
//!
//! - Supports UTF-8-formatted source code
//! - Supports multi-line comments
//! - Doesn't need a special `EOF` syntax token
//! - Rust-style error handling with `Result`

mod error;
mod scanner;
mod token;

pub use crate::error::TokenizerError;
use crate::scanner::Scanner;
pub use crate::token::{Token, TokenType};

/// Converts Lox source code into syntax tokens.
///
/// The source code is required to outlive the resultant syntax
/// tokens, as the tokens contain references to the parts of code they
/// were constructed from.
///
/// # Examples
///
/// Converting valid Lox code into syntax tokens:
///
/// ```
/// # use rlox_tokenizer::{tokenize, Token, TokenType};
/// let source = "var номер = (42);";
/// let tokens = tokenize(&source).unwrap();
///
/// let token_types: Vec<TokenType> = tokens.iter().map(|&t| t.token_type).collect();
/// assert_eq!(
///     token_types,
///     vec![
///         TokenType::Var,
///         TokenType::Identifier,
///         TokenType::Equal,
///         TokenType::LeftParen,
///         TokenType::Number,
///         TokenType::RightParen,
///         TokenType::Semicolon,
///     ]
/// );
///
/// let lexemes: Vec<&str> = tokens.iter().map(|&t| t.lexeme).collect();
/// assert_eq!(lexemes, vec!["var", "номер", "=", "(", "42", ")", ";"]);
///
/// let grapheme_offsets: Vec<usize> = tokens.iter().map(|&t| t.offset).collect();
/// assert_eq!(grapheme_offsets, vec![0, 4, 10, 12, 13, 15, 16]);
/// ```
///
/// Unterminated strings result in an error:
///
/// ```
/// # use rlox_tokenizer::{tokenize, Token, TokenType, TokenizerError};
/// let source = "var x = \"";
/// assert!(tokenize(&source).is_err());
/// ```
///
/// # Implementation Details
///
/// The reference C implementation of the Lox scanner/tokenizer
/// operates on basic C-style strings (`*char`) where an individual
/// character can be retrieved just by dereferencing since the whole
/// "string" is really an array of bytes.
///
/// This works great, up until your "characters" are no longer `u8` in
/// size, which is what happens when you encode in UTF-8, the default
/// character encoding for Rust's `&str` and `String` types. In Rust,
/// you can't pretend that a string is a simple array of `char`, where
/// `char` basically an alias for `u8`, like in C. Rust `char`s are
/// *four* bytes in size, as opposed to just one, which is why trying
/// to index into a Rust string byte-by-byte doesn't work: you won't
/// get a "character" unless your string is pure ASCII.
///
/// Worse yet, a Rust `char` is not necessarily what a normal person
/// would consider to be a "character". This example from the Rust
/// documentation explains it best:
///
/// ```
/// let mut chars = "é".chars();
/// // U+00e9: 'latin small letter e with acute'
/// assert_eq!(Some('\u{00e9}'), chars.next());
/// assert_eq!(None, chars.next());
///
/// let mut chars = "é".chars();
/// // U+0065: 'latin small letter e'
/// assert_eq!(Some('\u{0065}'), chars.next());
/// // U+0301: 'combining acute accent'
/// assert_eq!(Some('\u{0301}'), chars.next());
/// assert_eq!(None, chars.next());
/// ```
///
/// Basically: what you or I consider a "character" within a string
/// could actually be made up of multiple Rust `char`s, which means if
/// we want to be able to index into our UTF-8 Lox source code
/// "character-by-character", like the C implementation is able to do
/// with its ASCII strings, we need a different representation. Enter
/// the
/// [`unicode-segmentation`](https://crates.io/crates/unicode-segmentation)
/// crate.
///
/// `unicode-segmentation` allows us to process a Rust UTF-8 string
/// into an iterator over graphemes, which are basically the
/// "characters" I've been putting in air quotes this whole time. We
/// can then convert our iterator into a `Vec<(usize, &str)>`, where
/// the `usize` is the byte offset in the source code where the
/// grapheme begins, and the `&str` is the grapheme itself. We can use
/// that byte offset to slice into the source code, since our `Token`
/// struct needs a reference to the actual piece of the source code it
/// came from.
///
/// In theory, there should only be one copy of the source code in
/// memory at any time, which is great!
pub fn tokenize(source: &str) -> Result<Vec<Token<'_>>, TokenizerError> {
    let mut scanner = Scanner::new(source);
    let mut tokens: Vec<Token<'_>> = Vec::new();

    while let Some(token) = scanner.next_token()? {
        tokens.push(token);
    }

    Ok(tokens)
}

/// Calculates a line and column number.
///
/// Note that this will walk through `source` to the given offset in
/// order to calculate line breaks, so it can be relatively slow. This
/// method is intended to be used for error handling.
///
/// # Examples:
///
/// Finding the line and column number of a syntax token by its offset:
///
/// ```
/// # use rlox_tokenizer::{tokenize, calculate_location, Token};
/// let source = r#"var my_v4r = 21.1;
/// class MyClass {}
/// "#;
///
/// let tokens = tokenize(&source).unwrap();
/// # assert_eq!(tokens[6].lexeme, "MyClass");
/// let identifier_token = tokens[6];
/// assert_eq!(calculate_location(&source, identifier_token.offset), (2, 7));
///
/// # assert_eq!(tokens[0].lexeme, "var");
/// let var_token = tokens[0];
/// assert_eq!(calculate_location(&source, var_token.offset), (1, 1));
/// ```
///
/// # Panics
///
/// If the `grapheme_offset` isn't within the bounds of `source`'s graphemes.
pub fn calculate_location(source: &str, grapheme_offset: usize) -> (usize, usize) {
    use unicode_segmentation::UnicodeSegmentation;

    if source.is_empty() {
        panic!("can't calculate a line/column for an empty string");
    }

    let mut graphemes = UnicodeSegmentation::graphemes(source, true);
    let mut i = 0;

    let mut line = 1;
    let mut col = 1;
    while let Some(grapheme) = graphemes.next() {
        if i >= grapheme_offset {
            // Early break if we're about to run into the grapheme itself
            break;
        }

        match grapheme {
            "\n" | "\r" => {
                line += 1;
                col = 1;
            }
            _ => {
                col += 1;
            }
        }

        i += 1;
    }

    (line, col)
}
