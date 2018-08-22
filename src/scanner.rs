use crate::calculate_location;
use crate::error::TokenizerError;
use crate::token::TokenType::*;
use crate::token::{Token, TokenType};

use unicode_segmentation::UnicodeSegmentation;

/// Internal structure for scanning through Lox source code
/// grapheme-by-grapheme to produce `Token`s.
pub struct Scanner<'a> {
    /// The original source code, expected to outlive this struct
    source: &'a str,
    /// `GraphemeIndices`, tuples of byte offsets and graphemes
    graphemes: Vec<(usize, &'a str)>,
    /// Index of the starting grapheme of the lexeme
    start: usize,
    /// Index of the current grapheme of the lexeme
    // TODO: is it the current grapheme? Or the exclusive next
    // grapheme? Do we index exclusively with this variable?
    current: usize,
}

impl<'a> Scanner<'a> {
    /// Creates a new `Scanner`.
    pub fn new(source: &'a str) -> Scanner<'a> {
        // In theory we'd want to just use the iterator, but since we need
        // multiple graphemes of lookahead, it's actually easier to just
        // do an O(n) operation and make a `Vec`.
        let graphemes =
            UnicodeSegmentation::grapheme_indices(source, true).collect::<Vec<(usize, &str)>>();

        Scanner {
            source,
            graphemes,
            start: 0,
            current: 0,
        }
    }

    /// Advances the `Scanner` forward, returning a `Token`.
    ///
    /// # Returns
    ///
    /// `Err` if the source code is syntactically invalid/unparseable,
    /// `Ok(None)` if the `Scanner` can't find any more `Token`s.
    pub fn next_token(&mut self) -> Result<Option<Token<'a>>, TokenizerError> {
        self.skip_ignorables();

        if self.at_end() {
            return Ok(None);
        }

        // Fetching a single grapheme shouldn't ever fail here
        match self.take().unwrap() {
            // Always 1-grapheme matches
            "(" => Ok(Some(self.make_token(LeftParen))),
            ")" => Ok(Some(self.make_token(RightParen))),
            "{" => Ok(Some(self.make_token(LeftBrace))),
            "}" => Ok(Some(self.make_token(RightBrace))),
            ";" => Ok(Some(self.make_token(Semicolon))),
            "," => Ok(Some(self.make_token(Comma))),
            "." => Ok(Some(self.make_token(Dot))),
            "-" => Ok(Some(self.make_token(Minus))),
            "+" => Ok(Some(self.make_token(Plus))),
            "/" => Ok(Some(self.make_token(Slash))),
            "*" => Ok(Some(self.make_token(Star))),

            // 1 or maybe 2-grapheme matches
            "!" => {
                if self.take_if("=") {
                    Ok(Some(self.make_token(BangEqual)))
                } else {
                    Ok(Some(self.make_token(Bang)))
                }
            }
            "=" => {
                if self.take_if("=") {
                    Ok(Some(self.make_token(EqualEqual)))
                } else {
                    Ok(Some(self.make_token(Equal)))
                }
            }
            "<" => {
                if self.take_if("=") {
                    Ok(Some(self.make_token(LessEqual)))
                } else {
                    Ok(Some(self.make_token(Less)))
                }
            }
            ">" => {
                if self.take_if("=") {
                    Ok(Some(self.make_token(GreaterEqual)))
                } else {
                    Ok(Some(self.make_token(Greater)))
                }
            }

            // Literals
            "\"" => Ok(Some(self.make_string_literal()?)),
            g if is_ascii_digit(g) => Ok(Some(self.make_number_literal())),

            // Identifiers
            // (number literal case must come before this)
            g if is_alphabetic(g) => Ok(Some(self.make_identifier())),

            g => {
                let msg = format!("unexpected symbol: {}", g);
                let (line, col) = calculate_location(self.source, self.current - 1);

                Err(TokenizerError { line, col, msg })
            }
        }
    }

    /// Checks if the `Scanner` can extract another `Token`.
    fn at_end(&self) -> bool {
        // `start` must always be a valid index into the list of
        // graphemes.

        // This works so long as the actual token creation method
        // forbids extracting the same lexeme more than once, i.e, it
        // advances the `start` and `current` indices whenever you
        // make a new token with a lexeme.
        self.start >= self.graphemes.len() || self.current >= self.graphemes.len()
    }

    // ================================
    // METHODS FOR EXTRACTING GRAPHEMES
    // ================================
    // The following methods all have to do with looking for, testing
    // against, and retrieving graphemes from our collection of
    // grapheme indices. So if you're unsure what these methods do
    // based on their name alone, just mentally append "grapheme" to
    // the end of it.

    fn peek(&self) -> Option<&str> {
        if self.at_end() {
            None
        } else {
            Some(self.graphemes[self.current].1)
        }
    }

    fn peek_is(&self, expected: &str) -> bool {
        if self.at_end() {
            false
        } else {
            self.graphemes[self.current].1 == expected
        }
    }

    fn peek_next(&self) -> Option<&str> {
        if self.current + 1 >= self.graphemes.len() {
            None
        } else {
            Some(self.graphemes[self.current + 1].1)
        }
    }

    fn peek_next_is(&self, expected: &str) -> bool {
        if self.current + 1 >= self.graphemes.len() {
            false
        } else {
            self.graphemes[self.current + 1].1 == expected
        }
    }

    fn take(&mut self) -> Option<&str> {
        if self.at_end() {
            None
        } else {
            self.current += 1;
            Some(self.graphemes[self.current - 1].1)
        }
    }

    fn take_if(&mut self, expected: &str) -> bool {
        if self.peek_is(expected) {
            self.take();
            true
        } else {
            false
        }
    }

    // ==============================
    // METHODS FOR EXTRACTING LEXEMES
    // ==============================

    /// Advances the `Scanner` past whitespace, newlines, and comments
    /// until it is either at the end of the source code or it points
    /// to a valid grapheme.
    fn skip_ignorables(&mut self) {
        while let Some(current) = self.peek() {
            match current {
                // Whitespace AND newlines
                g if is_whitespace(g) => {
                    self.take();
                }

                // Comments
                "/" => {
                    if self.peek_next_is("/") {
                        // Skip to end of line or EOF
                        while let Some(grapheme) = self.take() {
                            if is_newline(grapheme) {
                                break;
                            }
                        }
                    } else if self.peek_next_is("*") {
                        self.skip_multiline_comments();
                    }
                }

                _ => {
                    // Reached a non-ignorable character: we're done!
                    break;
                }
            }
        }

        // Re-sync the start and current indices
        // `start` needs to point to the start of a lexeme
        self.start = self.current;
    }

    /// Advances the `Scanner` past multiline comments until it is
    /// either at the end of the source code or it points to a valid
    /// grapheme.
    ///
    /// Expects the current grapheme index to point to the opening
    /// slash "/" of the comment.
    fn skip_multiline_comments(&mut self) {
        // We know the current and next graphemes are "/*"
        self.take();
        self.take();

        // We already have one opening comment marker
        let mut stack: Vec<&'static str> = vec!["/*"];
        
        while let Some(current) = self.peek() {
            if current == "/" && self.peek_next_is("*") {
                // Opening comment
                stack.push("/*");
                self.take();
                self.take();
            } else if current == "*" && self.peek_next_is("/") {
                // Closing comment
                stack.pop();
                self.take();
                self.take();
                
                if stack.is_empty() {
                    // Every "/*" found its "*/"
                    return;
                }
            } else {
                // Consume it, it's part of the comment
                self.take();
            }
        }
    }

    /// Constructs a new syntax `Token` using the current internal
    /// state of the `Scanner`.
    ///
    /// # Panics
    ///
    /// If there isnt't an available part of the source code to
    /// reference as a lexeme.
    fn make_token(&self, token_type: TokenType) -> Token<'a> {
        let start = self.graphemes[self.start].0;

        // Get exclusive index for the source code
        let end = if self.peek().is_none() {
            self.source.len()
        } else {
            self.graphemes[self.current].0
        };

        let lexeme = &self.source[start..end];

        Token {
            token_type,
            lexeme,
            offset: self.start,
        }
    }

    /// Constructs a new string literal syntax `Token`.
    ///
    /// # Returns
    ///
    /// `Err` if the string is unterminated.
    fn make_string_literal(&mut self) -> Result<Token<'a>, TokenizerError> {
        // Basically, we just need to move the `current` index to the
        // ending quote grapheme, make a new token, then make sure we
        // consume the end quote so it doesn't get seen a second time.

        // Push the `start` index forwards, since our final lexeme
        // shouldn't include the opening quote itself
        self.start += 1;
        // (`start` should now equal `current`)

        while let Some(grapheme) = self.peek() {
            if grapheme == "\"" {
                break;
            } else {
                self.take();
            }
        }

        if self.at_end() {
            // We moved the `start` index so move the offset back
            let (line, col) = calculate_location(self.source, self.start - 1);

            Err(TokenizerError {
                line,
                col,
                msg: "unterminated string".to_string(),
            })
        } else {
            let mut token = self.make_token(String);
            // We moved the `start` index so move the offset back
            token.offset = self.start - 1;

            // Remember to skip that final quote
            self.take();
            Ok(token)
        }
    }

    /// Constructs a new number literal syntax `Token`.
    fn make_number_literal(&mut self) -> Token<'a> {
        // FIXME: this is ugly

        // We know we just saw an ASCII digit.
        // Consume any following digits
        while let Some(grapheme) = self.peek() {
            if is_ascii_digit(grapheme) {
                self.take();
            } else {
                break;
            }
        }

        // Check for fractional part
        if self.peek_is(".") {
            if let Some(grapheme) = self.peek_next() {
                if is_ascii_digit(grapheme) {
                    // Don't forget to consume the "."
                    self.take();

                    while let Some(grapheme) = self.peek() {
                        if is_ascii_digit(grapheme) {
                            self.take();
                        } else {
                            break;
                        }
                    }
                }
            }
        }

        self.make_token(Number)
    }

    /// Constructs a new identifier syntax `Token`.
    fn make_identifier(&mut self) -> Token<'a> {
        // We just saw an alphabetic grapheme, consume any following ones
        while let Some(grapheme) = self.peek() {
            if is_alphabetic(grapheme) || is_ascii_digit(grapheme) {
                self.take();
            } else {
                break;
            }
        }

        let mut token = self.make_token(Identifier);
        token.token_type = match token.lexeme {
            "and" => And,
            "class" => Class,
            "else" => Else,
            "false" => False,
            "for" => For,
            "fun" => Fun,
            "if" => If,
            "nil" => Nil,
            "or" => Or,
            "print" => Print,
            "return" => Return,
            "super" => Super,
            "this" => This,
            "true" => True,
            "var" => Var,
            "while" => While,
            _ => Identifier,
        };

        token
    }
}

// ========================
// GRAPHEME UTILITY METHODS
// ========================

/// Equivalent of std::char::is_whitespace(), but for graphemes.
///
/// Note that newlines are considered to be whitespace.
fn is_whitespace(grapheme: &str) -> bool {
    grapheme.trim().is_empty()
}

/// Checks if a grapheme is a newline.
fn is_newline(grapheme: &str) -> bool {
    match grapheme {
        "\n" | "\r" => true,
        _ => false,
    }
}

/// Equivalent of std::char::is_alphabetic(), but for graphemes.
fn is_alphabetic(grapheme: &str) -> bool {
    if grapheme == "_" {
        // Underscores are valid identifier characters
        return true;
    }

    for character in grapheme.chars() {
        if !character.is_alphabetic() {
            return false;
        }
    }

    true
}

/// Equivalent of std::char::is_ascii_digit(), but for graphemes.
fn is_ascii_digit(grapheme: &str) -> bool {
    let chars: Vec<char> = grapheme.chars().collect();
    if chars.len() != 1 {
        false
    } else {
        chars[0].is_ascii_digit()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Utility method for getting the first grapheme of a string
    fn grapheme(s: &'static str) -> &str {
        use unicode_segmentation::UnicodeSegmentation;
        UnicodeSegmentation::graphemes(s, true).next().unwrap()
    }

    // NOTE: It's correct to assume the number of graphemes is equal
    // to the number of "characters" you see. This is not true when
    // thinking in terms of Rust's `char` type.

    #[test]
    fn at_end_of_empty_string() {
        let s = Scanner::new("");
        assert!(s.at_end())
    }

    #[test]
    fn not_at_end_of_nonempty_string() {
        let s = Scanner::new("Hello");
        assert!(!s.at_end())
    }

    #[test]
    fn not_at_end_partially_finished_scanner() {
        let mut s = Scanner::new("Olá");
        s.take();
        s.take();

        assert!(!s.at_end())
    }

    #[test]
    fn at_end_finished_scanner() {
        let mut s = Scanner::new("Olá");
        s.take();
        s.take();
        s.take();

        assert!(s.at_end())
    }

    // ==============================
    // TESTS FOR EXTRACTING GRAPHEMES
    // ==============================

    #[test]
    fn take_empty_string_yields_none() {
        let mut s = Scanner::new("");
        assert!(s.take().is_none());
    }

    #[test]
    fn take_nonempty_string_yields_graphemes() {
        let mut s = Scanner::new("Olá");

        assert_eq!(s.take(), Some("O"));
        assert_eq!(s.take(), Some("l"));
        assert_eq!(s.take(), Some("á"));
        assert!(s.take().is_none());
    }

    #[test]
    fn take_if_advances_scanner() {
        let mut s = Scanner::new("Olá");
        s.take();
        s.take();

        assert!(s.take_if("á"));
        assert!(s.take().is_none());
    }

    #[test]
    fn take_if_doesnt_advance_scanner() {
        let mut s = Scanner::new("Olá");
        s.take();
        s.take();

        assert!(!s.take_if("a"));
        assert_eq!(s.take(), Some("á"));
    }

    #[test]
    fn peek_next_nonempty_string_yields_grapheme() {
        let s = Scanner::new("Hello");
        assert_eq!(s.peek_next(), Some("e"));
    }

    #[test]
    fn peek_next_short_string_yields_none() {
        let s = Scanner::new("H");
        assert!(s.peek_next().is_none());
    }

    #[test]
    fn peek_next_empty_string_yields_none() {
        let s = Scanner::new("");
        assert!(s.peek_next().is_none());
    }

    #[test]
    fn peek_next_is_true() {
        let s = Scanner::new("Hello");
        assert!(s.peek_next_is("e"));
    }

    #[test]
    fn peek_next_is_false() {
        let s = Scanner::new("Hello");
        assert!(!s.peek_next_is("l"));
    }

    #[test]
    fn peek_is_true() {
        let s = Scanner::new("Hello");
        assert!(s.peek_is("H"));
    }

    #[test]
    fn peek_is_false() {
        let s = Scanner::new("Hello");
        assert!(!s.peek_is("e"));
    }

    #[test]
    fn peek_nonempty_string_yields_grapheme() {
        let s = Scanner::new("Hello");
        assert_eq!(s.peek(), Some("H"));
    }

    #[test]
    fn peek_empty_string_yields_none() {
        let s = Scanner::new("");
        assert!(s.peek().is_none());
    }

    // ============================
    // TESTS FOR EXTRACTING LEXEMES
    // ============================

    #[test]
    fn make_identifier_nonkeyword_ascii() {
        let mut s = Scanner::new("Hello");
        // Remember to consume initial alphabetic grapheme
        s.take();

        let expected = Token {
            token_type: Identifier,
            lexeme: "Hello",
            offset: 0,
        };

        assert_eq!(s.make_identifier(), expected);
    }

    #[test]
    fn make_identifier_nonkeyword_unicode() {
        let mut s = Scanner::new("Здравствуйте");
        // Remember to consume initial alphabetic grapheme
        s.take();

        let expected = Token {
            token_type: Identifier,
            lexeme: "Здравствуйте",
            offset: 0,
        };

        assert_eq!(s.make_identifier(), expected);
    }

    #[test]
    fn make_identifier_keyword() {
        let mut s = Scanner::new("var");
        // Remember to consume initial alphabetic grapheme
        s.take();

        let expected = Token {
            token_type: Var,
            lexeme: "var",
            offset: 0,
        };

        assert_eq!(s.make_identifier(), expected);
    }

    #[test]
    fn make_integer_literal() {
        let mut s = Scanner::new("123abc");
        // Consume initial digit
        s.take();

        let expected = Token {
            token_type: Number,
            lexeme: "123",
            offset: 0,
        };

        assert_eq!(s.make_number_literal(), expected);
    }

    #[test]
    fn make_decimal_literal() {
        let mut s = Scanner::new("1.0012");
        // Consume initial and digit
        s.take();

        let expected = Token {
            token_type: Number,
            lexeme: "1.0012",
            offset: 0,
        };

        assert_eq!(s.make_number_literal(), expected);
    }

    #[test]
    fn make_string_literal() {
        let mut s = Scanner::new("\t\"Hello\"");
        s.skip_ignorables();

        // Don't forget to consume the starting open quote
        s.take();

        let expected = Token {
            token_type: String,
            lexeme: "Hello",
            offset: 1,
        };

        assert_eq!(s.make_string_literal(), Ok(expected));
    }

    #[test]
    fn make_string_literal_empty_literal() {
        let mut s = Scanner::new("\"\"");
        // Don't forget to consume the starting open quote
        s.take();

        let expected = Token {
            token_type: String,
            lexeme: "",
            offset: 0,
        };

        assert_eq!(s.make_string_literal(), Ok(expected));
    }

    #[test]
    fn make_string_literal_unterminated() {
        let mut s = Scanner::new("\"unterminated!");
        // Don't forget to consume the starting open quote
        s.take();

        assert!(s.make_string_literal().is_err());
    }

    #[test]
    #[should_panic]
    fn create_new_token_empty_string() {
        // This situation shouldn't happen in ordinary code, but it's
        // nice to have all the edge cases covered

        let s = Scanner::new("");
        assert!(s.at_end());
        assert!(s.peek().is_none());

        let expected = Token {
            token_type: Identifier,
            lexeme: "",
            offset: 0,
        };

        assert_eq!(s.make_token(Identifier), expected);
    }

    #[test]
    fn create_new_token_at_end() {
        let mut s = Scanner::new("Hello");
        s.take();
        s.take();
        s.take();
        s.take();
        s.take();
        assert!(s.at_end());

        assert_eq!(s.graphemes[s.start].1, "H");
        assert!(s.peek().is_none());

        let expected = Token {
            token_type: Identifier,
            lexeme: "Hello",
            offset: 0,
        };

        assert_eq!(s.make_token(Identifier), expected);
    }

    #[test]
    fn create_new_token_not_at_end() {
        let mut s = Scanner::new("Hello there");
        s.take();
        s.take();
        s.take();
        s.take();
        s.take();
        assert!(!s.at_end());

        // start should point to "H", current should point to " "
        assert_eq!(s.graphemes[s.start].1, "H");
        assert_eq!(s.graphemes[s.current].1, " ");

        let expected = Token {
            token_type: Identifier,
            lexeme: "Hello",
            offset: 0,
        };

        assert_eq!(s.make_token(Identifier), expected);
    }

    // =========================
    // TESTS FOR UTILITY METHODS
    // =========================

    #[test]
    fn ascii_digit_graphemes() {
        let graphemes: Vec<&'static str> = vec!["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];

        for grapheme in &graphemes {
            assert!(is_ascii_digit(grapheme));
        }
    }

    #[test]
    fn nonascii_digit_graphemes() {
        let graphemes: Vec<&'static str> = vec!["৬", "٣", "ƒ", "H", "①"];

        for grapheme in &graphemes {
            assert!(!is_ascii_digit(grapheme));
        }
    }

    #[test]
    fn alphabetic_graphemes() {
        let alphabetic_strings: Vec<&'static str> = vec![
            "foo",
            "ƒoo",
            "こんにちは",
            "안녕하세요",
            "Здравствуйте",
            "您好",
            "سلا",
            "สวั",
        ];

        for string in &alphabetic_strings {
            assert!(is_alphabetic(grapheme(string)));
        }
    }

    #[test]
    fn nonalphabetic_graphemes() {
        let nonalphabetic_strings: Vec<&'static str> = vec!["%", "@", "💝"];

        for string in &nonalphabetic_strings {
            assert!(!is_alphabetic(grapheme(string)));
        }
    }

    #[test]
    fn skip_leading_multiline_comment() {
        let source = r#"/* This is a multi
line comment that spans
several lines */

B
"#;
        let mut s = Scanner::new(source);
        s.skip_ignorables();

        assert_eq!(s.peek(), Some("B"));
    }

    #[test]
    fn skip_inner_multiline_comment() {
        let source = r#"A
/* This is a multi
line comment that spans
several lines */
B
"#;
        let mut s = Scanner::new(source);
        // Skip the leading grapheme
        s.take();
        s.skip_ignorables();

        assert_eq!(s.peek(), Some("B"));
    }

    #[test]
    fn skip_inline_multiline_comment() {
        let source = "A /* inline multiline comment */ B";
        let mut s = Scanner::new(source);
        // Skip the leading grapheme
        s.take();
        s.skip_ignorables();

        assert_eq!(s.peek(), Some("B"));
    }

    #[test]
    fn skip_nesting_multiline_comment() {
        let source = r#"/* This is a multiline comment
/* it has /* nested comments */ */ inside it */
B"#;
        let mut s = Scanner::new(source);
        s.skip_ignorables();

        assert_eq!(s.peek(), Some("B"));
    }

    #[test]
    fn skip_leading_line_comment() {
        let mut s = Scanner::new(" // Comment\r Hello");
        s.skip_ignorables();

        assert_eq!(s.peek(), Some("H"));
    }

    #[test]
    fn skip_inner_line_comment() {
        let mut s = Scanner::new("Hi\n// Comment \n  There ");
        s.take();
        s.take();
        s.skip_ignorables();
        assert_eq!(s.peek(), Some("T"));
    }

    #[test]
    fn skip_ending_line_comment() {
        let mut s = Scanner::new("Hi\n// Comment \n");
        s.take();
        s.take();

        assert!(s.peek().is_some());
        s.skip_ignorables();
        assert!(s.peek().is_none());
    }

    #[test]
    fn skip_no_whitespace() {
        let mut s = Scanner::new("Hello");
        s.skip_ignorables();

        assert_eq!(s.take(), Some("H"));
    }

    #[test]
    fn skip_leading_whitespace() {
        let mut s = Scanner::new("\t  \r  Hello");
        s.skip_ignorables();

        assert_eq!(s.take(), Some("H"));
    }

    #[test]
    fn skip_inner_whitespace() {
        let mut s = Scanner::new("Hi \t\r there");
        s.take();
        s.take();
        s.skip_ignorables();

        assert_eq!(s.take(), Some("t"));
    }

    #[test]
    fn skip_trailing_whitespace() {
        let mut s = Scanner::new("Hi\t \r");
        s.take();
        s.take();

        assert!(s.peek().is_some());
        s.skip_ignorables();
        assert!(s.peek().is_none());
        assert!(s.at_end());
    }
}
