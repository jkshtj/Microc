use derive_more::Display;

#[allow(unused)]
#[derive(Debug, Eq, PartialEq, Display, Copy, Clone)]
pub enum TokenType {
    KEYWORD,
    OPERATOR,
    LITERAL,
    IDENTIFIER,
    DISCARDABLE,
}

#[allow(unused)]
#[derive(Debug, PartialEq, Display, Clone)]
pub enum Token {
    // Identifiers
    #[display(fmt = "{}", _1)]
    IDENTIFIER(TokenType, String),

    // Literals
    #[display(fmt = "{}", _1)]
    INTLITERAL(TokenType, u32),
    #[display(fmt = "{}", _1)]
    FLOATLITERAL(TokenType, f64),
    #[display(fmt = "{}", _1)]
    STRINGLITERAL(TokenType, String),

    // Keywords
    #[display(fmt = "{}", _1)]
    PROGRAM(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    BEGIN(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    END(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    FUNCTION(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    READ(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    WRITE(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    IF(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    ELSE(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    FI(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    FOR(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    ROF(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    RETURN(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    INT(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    VOID(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    STRING(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    FLOAT(TokenType, &'static str),

    // Operators
    #[display(fmt = "{}", _1)]
    ASSIGNMENT(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    ADD(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    SUB(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    MUL(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    DIV(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    EQ(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    NE(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    LT(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    GT(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    LTE(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    GTE(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    LPAREN(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    RPAREN(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    SEMICOLON(TokenType, &'static str),
    #[display(fmt = "{}", _1)]
    COMMA(TokenType, &'static str),
}

#[cfg(test)]
mod test {
    use crate::token::{Token, TokenType};

    #[test]
    fn token_returns_correct_value() {
        let t = Token::INT(TokenType::KEYWORD, "INT");

        assert_eq!("INT", t.to_string());
    }
}
