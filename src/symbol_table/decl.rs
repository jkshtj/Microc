#![allow(dead_code)]

use crate::symbol_table::Symbol;
use derive_more::Display;

#[derive(Debug, Display, PartialEq, Clone)]
#[display(fmt = "name {} type STRING value {}\n", name, value)]
pub struct StringDecl {
    name: String,
    value: String,
}

impl StringDecl {
    pub fn new(name: String, value: String) -> Self {
        StringDecl { name, value }
    }

    pub fn get_name(&self) -> &str {
        self.name.as_str()
    }
}

#[derive(Debug, Display, PartialEq, Clone)]
#[display(fmt = "name {} type INT\n", name)]
pub struct IntDecl {
    name: String,
}

impl IntDecl {
    pub fn new(name: String) -> Self {
        IntDecl {
            name,
        }
    }

    pub fn get_name(&self) -> &str {
        self.name.as_str()
    }
}

#[derive(Debug, Display, PartialEq, Clone)]
#[display(fmt = "name {} type FLOAT\n", name)]
pub struct FloatDecl {
    name: String,
}

impl FloatDecl {
    pub fn new(name: String) -> Self {
        FloatDecl {
            name,
        }
    }

    pub fn get_name(&self) -> &str {
        self.name.as_str()
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
    use crate::token::TokenType;

    #[test]
    fn string_entry_print_format() {
        let entry = StringDecl {
            name: "id1".to_owned(),
            value: "value1".to_owned(),
        };

        let expected = "name id1 type STRING value value1\n";
        assert_eq!(expected, entry.to_string());
    }

    #[test]
    fn int_entry_print_format() {
        let entry = IntDecl {
            name: "int1".to_owned(),
        };

        let expected = "name int1 type INT\n";
        assert_eq!(expected, entry.to_string());
    }

    #[test]
    fn float_entry_print_format() {
        let entry = FloatDecl {
            name: "float1".to_owned(),
        };

        let expected = "name float1 type FLOAT\n";
        assert_eq!(expected, entry.to_string());
    }
}