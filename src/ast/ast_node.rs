use crate::symbol_table::SymbolType;

#[derive(Debug)]
pub enum AddOp {
    Add,
    Sub,
}

#[derive(Debug)]
pub enum MulOp {
    Mul,
    Div,
}

#[derive(Debug)]
pub enum AstNode {
    Identifier {
        id: String,
        sym_type: SymbolType,
    },
    IntLiteral(i32),
    FloatLiteral(f64),
    ReadExpr(Vec<AstNode>),
    WriteExpr(Vec<AstNode>),
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
        lhs: Box<AstNode>,
        rhs: Box<AstNode>,
    },
    None,
}
