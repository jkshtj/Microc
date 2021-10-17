use crate::types::Identifier;

#[derive(Debug, Copy, Clone)]
pub enum AddOp {
    Add,
    Sub,
}

#[derive(Debug, Copy, Clone)]
pub enum MulOp {
    Mul,
    Div,
}

#[derive(Debug)]
pub enum AstNode {
    Id(Identifier),
    IntLiteral(i32),
    FloatLiteral(f64),
    ReadExpr(Vec<Identifier>),
    WriteExpr(Vec<Identifier>),
    AddExpr {
        op: AddOp,
        lhs: Box<AstNode>,
        rhs: Box<AstNode>,
    },
    MulExpr {
        op: MulOp,
        lhs: Box<AstNode>,
        rhs: Box<AstNode>,
    },
    AssignExpr {
        lhs: Identifier,
        rhs: Box<AstNode>,
    },
    None,
}
