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

/// Represents the comparison
/// operation in a boolean expression.
#[derive(Debug, Copy, Clone)]
pub enum CmpOp {
    /// Less than
    Lt,
    /// Greater than
    Gt,
    /// Equal to
    Eq,
    /// Not equal to
    Ne,
    /// Less than or equal to
    Lte,
    /// Greater than or equal to
    Gte,
}

/// Represents an identifier
/// for a declared symbol.
#[derive(Debug, Clone)]
pub struct Identifier {
    pub id: String,
    pub sym_type: SymbolType,
}

/// Statements in Microc.
#[derive(Debug, Clone)]
pub enum Stmt {
    Read(Vec<Identifier>),
    Write(Vec<Identifier>),
    Assign(Assignment),
    If {
        condition: Condition,
        then_block: Vec<Stmt>,
        else_block: Vec<Stmt>,
    },
    For {
        init: Option<Assignment>,
        condition: Condition,
        incr: Option<Assignment>,
        body: Vec<Stmt>,
    }
}

/// An assignment, which exists only
/// for building different statements
/// made up of assign semantics, such as,
/// assign, if and for statements.
#[derive(Debug, Clone)]
pub struct Assignment {
    pub lhs: Identifier,
    pub rhs: Expr,
}

/// A boolean expression that evaluates
/// to either true or false.
#[derive(Debug, Clone)]
pub struct Condition {
    pub cmp_op: CmpOp,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// Math expressions in Microc
/// that evaluate to a numeric
/// value.
#[derive(Debug, Clone)]
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
