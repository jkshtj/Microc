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

pub mod visit {
    use super::*;

    pub trait Visitor<T> {
        fn visit_identifier(&mut self, id: Identifier) -> T;
        fn visit_int_literal(&mut self, n: i32) -> T;
        fn visit_float_literal(&mut self, n: f64) -> T;
        fn visit_read_expression(&mut self, expr: Vec<Identifier>) -> T;
        fn visit_write_expr(&mut self, expr: Vec<Identifier>) -> T;
        fn visit_add_expr(&mut self, op: AddOp, lhs: Box<AstNode>, rhs: Box<AstNode>) -> T;
        fn visit_mul_expr(&mut self, op: MulOp, lhs: Box<AstNode>, rhs: Box<AstNode>) -> T;
        fn visit_assign_expr(&mut self, lhs: Identifier, rhs: Box<AstNode>) -> T;
    }
}
