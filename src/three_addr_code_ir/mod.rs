//! Three Address Code Intermediate representation
use crate::types::{Identifier, NumType};
use std::sync::atomic::{AtomicU64, Ordering};
use crate::ast::ast_node::{AstNode, AddOp, MulOp};
use crate::symbol_table::SymbolType;
use derive_more::Display;

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Copy, Clone, Display)]
#[display(fmt = "$T{}", _0)]
pub struct Temporary(u64);

impl Temporary {
    pub fn new() -> Self {
        Temporary(TEMP_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

#[derive(Debug, Clone, Display)]
pub enum LValue {
    Temp(Temporary),
    #[display(fmt = "{}", "_0.id")]
    Id(Identifier),
}

#[derive(Debug, Clone, Display)]
pub enum RValue {
    IntLiteral(i32),
    FloatLiteral(f64),
    StringLiteral(String),
}

#[derive(Debug, Clone, Display)]
pub enum Operand {
    LValue(LValue),
    RValue(RValue),
    None,
}

impl From<Temporary> for Operand {
    fn from(val: Temporary) -> Self {
        Operand::LValue(LValue::Temp(val))
    }
}

impl From<Identifier> for Operand {
    fn from(val: Identifier) -> Self {
        Operand::LValue(LValue::Id(val))
    }
}

impl From<i32> for Operand {
    fn from(val: i32) -> Self {
        Operand::RValue(RValue::IntLiteral(val))
    }
}

impl From<f64> for Operand {
    fn from(val: f64) -> Self {
        Operand::RValue(RValue::FloatLiteral(val))
    }
}

impl From<String> for Operand {
    fn from(val: String) -> Self {
        Operand::RValue(RValue::StringLiteral(val))
    }
}

impl From<LValue> for Operand {
    fn from(lvalue: LValue) -> Self {
        Operand::LValue(lvalue)
    }
}

impl From<RValue> for Operand {
    fn from(rvalue: RValue) -> Self {
        Operand::RValue(rvalue)
    }
}

#[derive(Debug, Clone, Display)]
pub enum ThreeAddressCode {
    #[display(fmt = "ADDI {} {} {}", lhs, rhs, register)]
    Add {
        lhs: Operand,
        rhs: Operand,
        register: Temporary,
    },
    #[display(fmt = "SUBI {} {} {}", lhs, rhs, register)]
    Sub {
        lhs: Operand,
        rhs: Operand,
        register: Temporary,
    },
    #[display(fmt = "MULTI {} {} {}", lhs, rhs, register)]
    Mul {
        lhs: Operand,
        rhs: Operand,
        register: Temporary,
    },
    #[display(fmt = "DIVI {} {} {}", lhs, rhs, register)]
    Div {
        lhs: Operand,
        rhs: Operand,
        register: Temporary,
    },
    #[display(fmt = "STOREI {} {}", rhs, lhs)]
    Store {
        lhs: LValue,
        rhs: Operand,
    },
    #[display(fmt = "READI {}", "identifier.id")]
    Read {
        identifier: Identifier,
    },
    #[display(fmt = "WRITEI {}", "identifier.id")]
    Write {
        identifier: Identifier,
    },
}

// TODO: Should this be moved to common types?
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ResultType {
    String,
    Int,
    Float,
    None
}

impl From<SymbolType> for ResultType {
    fn from(symbol_type: SymbolType) -> Self {
        match symbol_type {
            SymbolType::String => ResultType::String,
            SymbolType::Num(t) => {
                match t {
                    NumType::Int => ResultType::Int,
                    NumType::Float => ResultType::Float,
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct CodeObject {
    pub result: Operand,
    pub result_type: ResultType,
    pub code_sequence: Vec<ThreeAddressCode>,
}

impl CodeObject {
    pub fn combined_result_type(left: ResultType, right: ResultType) -> ResultType {
        match (left, right) {
            (ResultType::Float, ResultType::Float) => ResultType::Float,
            (ResultType::Int, ResultType::Int) => ResultType::Int,
            (_, _) => panic!("Unsupported result type combination. Left: [{:?}], Right: [{:?}]", left, right),
        }
    }

    // TODO: Try implementing this Post-Order traversal recursively

    // TODO: Reimplement conversion of AST to 3AC IR using visitor pattern
    //  (https://rust-unofficial.github.io/patterns/patterns/behavioural/visitor.html)-
    //  - There should be a `Visit` trait, with a visit_* method for each variant of the AST.
    //  - 3AC should implement `Visit` to define what it does with each AST node that it sees.
    //    That is pretty much exactly what I'm doing right now with the match statement.
    //
    // Note - Visitor pattern does not care about traversal strategy. For instance I can
    //  traverse the AST using Pre-Order traversal and the visitor pattern will still apply.
    //  In fact if my visitor did not have to return a value from each visit_* call, I could
    //  have separated the traversal strategy into a separate method.
    pub fn walk_ast(ast: AstNode) -> Self {
        return match ast {
            AstNode::Id(identifier)  => {
                let result_type = identifier.sym_type.into();

                CodeObject {
                    result: identifier.into(),
                    result_type,
                    code_sequence: vec![]
                }
            },
            AstNode::IntLiteral(n) => {
                let register = Temporary::new();
                CodeObject {
                    result: register.into(),
                    result_type: ResultType::Int,
                    code_sequence: vec![ThreeAddressCode::Store {
                        lhs: LValue::Temp(register),
                        rhs: n.into(),
                    }]
                }
            },
            AstNode::FloatLiteral(n)  => {
                let register = Temporary::new();
                CodeObject {
                    result: register.into(),
                    result_type: ResultType::Float,
                    code_sequence: vec![ThreeAddressCode::Store {
                        lhs: LValue::Temp(register),
                        rhs: n.into(),
                    }]
                }
            },
            AstNode::ReadExpr(identifiers) => {
                let code_sequence = identifiers
                    .into_iter()
                    .map(|identifier| ThreeAddressCode::Read {
                        identifier,
                    })
                    .collect();

                CodeObject {
                    result: Operand::None,
                    result_type: ResultType::None,
                    code_sequence,
                }
            },
            AstNode::WriteExpr(identifiers) => {
                let code_sequence = identifiers
                    .into_iter()
                    .map(|identifier| ThreeAddressCode::Write {
                        identifier,
                    })
                    .collect();

                CodeObject {
                    result: Operand::None,
                    result_type: ResultType::None,
                    code_sequence,
                }
            },
            AstNode::AssignExpr {
                lhs,
                rhs
            } => {
                let rhs = Self::walk_ast(Box::into_inner(rhs));

                let (curr_operand, mut code_sequence) = (rhs.result, rhs.code_sequence);

                let assign_code = ThreeAddressCode::Store {
                    lhs: LValue::Id(lhs),
                    rhs: curr_operand
                };

                code_sequence.push(assign_code);

                CodeObject {
                    result: Operand::None,
                    result_type: ResultType::None,
                    code_sequence,
                }
            },
            AstNode::AddExpr {
                op,
                lhs,
                rhs
            } => {
                let lhs = Self::walk_ast(Box::into_inner(lhs));
                let rhs = Self::walk_ast(Box::into_inner(rhs));

                let result_type = Self::combined_result_type(lhs.result_type, rhs.result_type);
                let (curr_left_operand, mut left_code_seq) = (lhs.result, lhs.code_sequence);
                let (curr_right_operand, mut right_code_seq) = (rhs.result, rhs.code_sequence);

                let register = Temporary::new();

                let curr_code = match op {
                    AddOp::Add => ThreeAddressCode::Add {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        register,
                    },
                    AddOp::Sub => ThreeAddressCode::Sub {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        register,
                    }
                };

                left_code_seq.append(&mut right_code_seq);
                left_code_seq.push(curr_code);

                CodeObject {
                    result: register.into(),
                    result_type: result_type,
                    code_sequence: left_code_seq,
                }
            },
            AstNode::MulExpr {
                op,
                lhs,
                rhs
            } => {
                let lhs = Self::walk_ast(Box::into_inner(lhs));
                let rhs = Self::walk_ast(Box::into_inner(rhs));

                let result_type = Self::combined_result_type(lhs.result_type, rhs.result_type);
                let (curr_left_operand, mut left_code_seq) = (lhs.result, lhs.code_sequence);
                let (curr_right_operand, mut right_code_seq) = (rhs.result, rhs.code_sequence);

                let register = Temporary::new();

                let curr_code = match op {
                    MulOp::Mul => ThreeAddressCode::Mul {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        register,
                    },
                    MulOp::Div => ThreeAddressCode::Div {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        register,
                    }
                };

                left_code_seq.append(&mut right_code_seq);
                left_code_seq.push(curr_code);

                CodeObject {
                    result: register.into(),
                    result_type: result_type,
                    code_sequence: left_code_seq,
                }
            },
            AstNode::None => panic!("AST contains a `None` node. Cannot convert incomplete AST into a CodeObject"),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::ast::ast_node::{AstNode, AddOp, MulOp};
    use crate::symbol_table::SymbolType;
    use crate::types::NumType;
    use super::*;

    #[test]
    fn convert_simple_expression_ast_to_code_object() {
        // Expression => b*b + a
        // AST -
        //      (+)
        //      / \
        //    (*) (a)
        //   /  \
        // (b)  (b)
        let ast = AstNode::AddExpr {
            op: AddOp::Add,
            lhs: Box::new(AstNode::MulExpr {
                op: MulOp::Mul,
                lhs: Box::new(AstNode::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Int)
                })),
                rhs: Box::new(AstNode::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Int)
                })),
            }),
            rhs: Box::new(AstNode::Id(Identifier {
                id: "a".to_string(),
                sym_type: SymbolType::Num(NumType::Int)
            })),
        };

        let code_object = CodeObject::walk_ast(ast);

        dbg!(code_object.clone());

        assert!(matches!(code_object.result, Operand::LValue(LValue::Temp(_))));
        assert_eq!(ResultType::Int, code_object.result_type);
        assert_eq!(2, code_object.code_sequence.len());
    }
}
