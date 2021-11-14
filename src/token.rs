use derive_more::Display;

#[allow(unused)]
#[derive(Debug, Eq, PartialEq, Display, Copy, Clone)]
pub enum TokenType {
    Keyword,
    Operator,
    Literal,
    Identifier,
    Discardable,
}

#[allow(unused)]
#[derive(Debug, PartialEq, Display, Clone)]
pub enum Token {
    // Identifiers
    #[display(fmt = "{}", _1)]
    Identifier(TokenType, String),

    // Literals
    #[display(fmt = "{}", _1)]
    Intliteral(TokenType, u32),
    #[display(fmt = "{}", _1)]
    Floatliteral(TokenType, f64),
    #[display(fmt = "{}", _1)]
    Stringliteral(TokenType, String),

    // Keywords
    #[display(fmt = "{}", _1)]
    Program(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Begin(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    End(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Function(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Read(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Write(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    If(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Else(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Fi(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    For(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Rof(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Return(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Int(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Void(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    String(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Float(TokenType, &'static str),

    // Operators
    #[display(fmt = "{}", _1)]
    Assignment(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Add(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Sub(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Mul(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Div(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Eq(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Ne(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Lt(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Gt(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Lte(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Gte(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Lparen(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Rparen(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Semicolon(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    Comma(TokenType, &'static str),
}

#[cfg(test)]
mod test {
    use crate::token::{Token, TokenType};

    #[test]
    fn token_returns_correct_value() {
        let t = Token::Int(TokenType::Keyword, "INT");

        assert_eq!("INT", t.to_string());
    }
}
