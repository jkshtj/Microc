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
pub enum Stmt {
    Read(Vec<Identifier>),
    Write(Vec<Identifier>),
    Assign {
        lhs: Identifier,
        rhs: Box<Expr>,
    },
}

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
}

#[derive(Debug)]
pub enum AstNode {
    Stmt(Stmt),
    Expr(Expr),
    None,
}

pub mod visit {
    use super::*;

    pub trait Visitor<T> {
        fn visit_statement(&mut self, stmt: Stmt) -> T;
        fn visit_expression(&mut self, expr: Expr) -> T;
    }
}
