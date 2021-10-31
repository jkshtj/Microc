use crate::symbol_table::SymbolType;

/// Differentiates an addition `AddExpr` node
/// from a subtraction `AddExpr` node.
#[derive(Debug, Copy, Clone)]
pub enum AddOp {
    Add,
    Sub,
}

/// Differentiates an multiplication
/// `MulExpr` node from a division
/// `MulExpr` node.
#[derive(Debug, Copy, Clone)]
pub enum MulOp {
    Mul,
    Div,
}

/// Represents an identifier
/// for a declared symbol.
#[derive(Debug, Clone)]
pub struct Identifier {
    pub id: String,
    pub sym_type: SymbolType,
}

/// Statements in Microc.
#[derive(Debug)]
pub enum Stmt {
    Read(Vec<Identifier>),
    Write(Vec<Identifier>),
    Assign {
        lhs: Identifier,
        rhs: Box<Expr>,
    },
}

/// Expressions in Microc.
/// All expressions evaluate
/// to a value that can be assigned.
#[derive(Debug)]
pub enum Expr {
    Id(Identifier),
    IntLiteral(i32),
    FloatLiteral(f64),
    AddExpr {
        op: AddOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    MulExpr {
        op: MulOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    None,
}

/// Abstract syntax tree representation
/// for Microc.
#[derive(Debug)]
pub enum AstNode {
    Stmt(Stmt),
    Expr(Expr),
}

pub mod visit {
    use super::*;

    /// Visitor trait that must be implemented
    /// by different intermediate representations
    /// that can be generated from the AST
    /// representation of Microc.
    pub trait Visitor<T> {
        fn visit_statement(&mut self, stmt: Stmt) -> T;
        fn visit_expression(&mut self, expr: Expr) -> T;
    }
}
