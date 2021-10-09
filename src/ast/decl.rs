#![allow(dead_code)]

use crate::ast::token::{Token, TokenType};
use derive_more::Display;
use crate::symbol_table::Symbol;

#[derive(Debug, Display, PartialEq, Clone)]
#[display(fmt = "name {} type STRING value {}", name, value)]
pub struct StringDecl {
    name: Token,
    value: Token,
}

impl StringDecl {
    pub fn new(name: Token, value: Token) -> Self {
        StringDecl { name, value }
    }

    pub fn get_name(&self) -> &str {
        // TODO: Can we ensure that we only use the
        //  `Token::IDENTIFIER` type for initializing
        //  the name field?
        // Safe to unwrap cause we know that name
        // will always be of type `Token::IDENTIFIER`.
        self.name.get_name_if_identifier().unwrap()
    }
}

#[derive(Debug, Display, PartialEq, Clone)]
#[display(fmt = "name {} type INT", name)]
pub struct IntDecl {
    name: Token,
    value: Token,
}

impl IntDecl {
    pub fn new(name: Token) -> Self {
        IntDecl {
            name,
            value: Token::INTLITERAL(TokenType::LITERAL, 0),
        }
    }

    pub fn new_with_value(name: Token, value: Token) -> Self {
        IntDecl { name, value }
    }

    pub fn get_name(&self) -> &str {
        // TODO: Can we ensure that we only use the
        //  `Token::IDENTIFIER` type for initializing
        //  the name field?
        // Safe to unwrap cause we know that name
        // will always be of type `Token::IDENTIFIER`.
        self.name.get_name_if_identifier().unwrap()
    }
}

#[derive(Debug, Display, PartialEq, Clone)]
#[display(fmt = "name {} type FLOAT", name)]
pub struct FloatDecl {
    name: Token,
    value: Token,
}

impl FloatDecl {
    pub fn new(name: Token) -> Self {
        FloatDecl {
            name,
            value: Token::FLOATLITERAL(TokenType::LITERAL, 0.0),
        }
    }

    pub fn new_with_value(name: Token, value: Token) -> Self {
        FloatDecl { name, value }
    }

    pub fn get_name(&self) -> &str {
        // TODO: Can we ensure that we only use the
        //  `Token::IDENTIFIER` type for initializing
        //  the name field?
        // Safe to unwrap cause we know that name
        // will always be of type `Token::IDENTIFIER`.
        self.name.get_name_if_identifier().unwrap()
    }
}

macro_rules! into_symbol {
    ($type: ty, $symbol_type: path) => {
        impl From<$type> for Symbol {
            fn from(t: $type) -> Symbol {
                $symbol_type(t)
            }
        }
    };
}

// Impls for into `Symbol`
into_symbol!(StringDecl, Symbol::String);
into_symbol!(IntDecl, Symbol::Int);
into_symbol!(FloatDecl, Symbol::Float);

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::token::TokenType;

    #[test]
    fn string_entry_print_format() {
        let entry = StringDecl {
            name: Token::IDENTIFIER(
                TokenType::IDENTIFIER,
                "id1".to_owned(),
            ),
            value: Token::STRINGLITERAL(
                TokenType::LITERAL,
                "value1".to_owned(),
            )
        };

        let expected = "name: id1 type: STRING value: value1\n";
        assert_eq!(expected, entry.to_string());
    }

    #[test]
    fn int_entry_print_format() {
        let entry = IntDecl {
            name: Token::IDENTIFIER(
                TokenType::IDENTIFIER,
                "int1".to_owned(),
            ),
            value: Token::INTLITERAL(
                TokenType::LITERAL,
                5,
            )
        };

        let expected = "name: int1 type: INT\n";
        assert_eq!(expected, entry.to_string());
    }

    #[test]
    fn float_entry_print_format() {
        let entry = FloatDecl {
            name: Token::IDENTIFIER(
                TokenType::IDENTIFIER,
                "float1".to_owned(),
            ),
            value: Token::FLOATLITERAL(
                TokenType::LITERAL,
                1.0,
            )
        };

        let expected = "name: float1 type: FLOAT\n";
        assert_eq!(expected, entry.to_string());
    }
}