use derive_more::Display;

use crate::three_addr_code_ir::{
    BinaryExprOperand, IdentF, IdentI, IdentS, LValueF, LValueI, Label, TempF, TempI,
};

#[derive(Debug, Clone, Display)]
pub enum ThreeAddressCode {
    #[display(fmt = "ADDI {} {} {}", lhs, rhs, temp_result)]
    AddI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempI,
    },
    #[display(fmt = "SUBI {} {} {}", lhs, rhs, temp_result)]
    SubI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempI,
    },
    #[display(fmt = "MULTI {} {} {}", lhs, rhs, temp_result)]
    MulI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempI,
    },
    #[display(fmt = "DIVI {} {} {}", lhs, rhs, temp_result)]
    DivI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempI,
    },
    #[display(fmt = "STOREI {} {}", rhs, lhs)]
    StoreI {
        lhs: LValueI,
        rhs: BinaryExprOperand,
    },
    #[display(fmt = "READI {}", identifier)]
    ReadI { identifier: IdentI },
    #[display(fmt = "WRITEI {}", identifier)]
    WriteI { identifier: IdentI },
    #[display(fmt = "ADDF {} {} {}", lhs, rhs, temp_result)]
    AddF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempF,
    },
    #[display(fmt = "SUBF {} {} {}", lhs, rhs, temp_result)]
    SubF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempF,
    },
    #[display(fmt = "MULTF {} {} {}", lhs, rhs, temp_result)]
    MulF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempF,
    },
    #[display(fmt = "DIVF {} {} {}", lhs, rhs, temp_result)]
    DivF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        temp_result: TempF,
    },
    #[display(fmt = "STOREF {} {}", rhs, lhs)]
    StoreF {
        lhs: LValueF,
        rhs: BinaryExprOperand,
    },
    #[display(fmt = "READF {}", identifier)]
    ReadF { identifier: IdentF },
    #[display(fmt = "WRITEF {}", identifier)]
    WriteF { identifier: IdentF },
    #[display(fmt = "WRITES {}", identifier)]
    WriteS { identifier: IdentS },
    #[display(fmt = "LABEL {}", _0)]
    Label(Label),
    #[display(fmt = "JUMP {}", _0)]
    Jump(Label),
    #[display(fmt = "GT {} {} {}", lhs, rhs, label)]
    Gt {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LT {} {} {}", lhs, rhs, label)]
    Lt {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "GE {} {} {}", lhs, rhs, label)]
    Gte {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LE {} {} {}", lhs, rhs, label)]
    Lte {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "NE {} {} {}", lhs, rhs, label)]
    Ne {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "EQ {} {} {}", lhs, rhs, label)]
    Eq {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
}

pub mod visit {
    use crate::ast::ast_node::visit::Visitor;
    use crate::ast::ast_node::{AddOp, Assignment, AstNode, CmpOp, Condition, Expr, MulOp, Stmt};
    use crate::symbol_table::{NumType, SymbolType};
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode::{
        Jump, Eq, Gt, Gte, Lt, Lte, Ne,
    };
    use crate::three_addr_code_ir::{
        BinaryExprOperand, IdentF, IdentI, LValueF, LValueI, Label, ResultType, TempF, TempI,
    };
    use typed_builder::TypedBuilder;

    #[derive(Debug, Clone, TypedBuilder)]
    #[builder(field_defaults(default, setter(strip_option)))]
    pub struct CodeObject {
        pub result: Option<BinaryExprOperand>,
        pub result_type: Option<ResultType>,
        pub jump_to: Option<Label>,
        #[builder(setter(!strip_option))]
        pub code_sequence: Vec<ThreeAddressCode>,
    }

    #[derive(Debug)]
    pub struct ThreeAddressCodeVisitor;

    impl ThreeAddressCodeVisitor {
        pub fn combined_result_type(left: ResultType, right: ResultType) -> ResultType {
            match (left, right) {
                (ResultType::Float, ResultType::Float) => ResultType::Float,
                (ResultType::Int, ResultType::Int) => ResultType::Int,
                (_, _) => panic!(
                    "Unsupported result type combination. Left: [{:?}], Right: [{:?}]",
                    left, right
                ),
            }
        }

        pub fn walk_ast(&mut self, ast: AstNode) -> CodeObject {
            match ast {
                AstNode::Stmt(stmt) => self.visit_statement(stmt),
                AstNode::Expr(expr) => self.visit_expression(expr),
            }
        }
    }

    // Note - Visitor pattern does not care about traversal strategy. For instance I can
    //  traverse the AST using Pre-Order traversal and the visitor pattern will still apply.
    //  In fact, if my visitor did not have to return a value from each visit_* call, I could
    //  have separated the traversal strategy into a separate method.
    // TODO: Can the Post-Order traversal of the AST be done iteratively?
    impl Visitor<CodeObject> for ThreeAddressCodeVisitor {
        fn visit_statement(&mut self, stmt: Stmt) -> CodeObject {
            match stmt {
                Stmt::Read(identifiers) => {
                    let code_sequence = identifiers
                        .into_iter()
                        .map(|identifier| match identifier.sym_type {
                            SymbolType::String => {
                                panic!("Unsupported operation: cannot READ into string identifier!")
                            }
                            SymbolType::Num(num_type) => match num_type {
                                NumType::Int => ThreeAddressCode::ReadI {
                                    identifier: identifier.into(),
                                },
                                NumType::Float => ThreeAddressCode::ReadF {
                                    identifier: identifier.into(),
                                },
                            },
                        })
                        .collect();

                    CodeObject::builder().code_sequence(code_sequence).build()
                }
                Stmt::Write(identifiers) => {
                    let code_sequence = identifiers
                        .into_iter()
                        .map(|identifier| match identifier.sym_type {
                            SymbolType::String => ThreeAddressCode::WriteS {
                                identifier: identifier.into(),
                            },
                            SymbolType::Num(num_type) => match num_type {
                                NumType::Int => ThreeAddressCode::WriteI {
                                    identifier: identifier.into(),
                                },
                                NumType::Float => ThreeAddressCode::WriteF {
                                    identifier: identifier.into(),
                                },
                            },
                        })
                        .collect();

                    CodeObject::builder().code_sequence(code_sequence).build()
                }
                Stmt::Assign(assignment) => self.visit_assignment(assignment),
                Stmt::If {
                    condition,
                    then_block,
                    else_block,
                } => {
                    let condition = self.visit_condition(condition);
                    // Unwrapping is safe here as the `jump_to` field
                    // of the returned `CodeObject`, from visiting a `Condition`
                    // is guaranteed to be set.
                    let else_label = condition.jump_to.unwrap();
                    let break_label = Label::new();
                    let mut code_sequence = condition.code_sequence;

                    // `then` block statements
                    then_block.into_iter().for_each(|stmt| {
                        code_sequence.append(&mut self.visit_statement(stmt).code_sequence);
                    });

                    // Jump to break_label
                    code_sequence.push(Jump(break_label));

                    // `else` block label
                    code_sequence.push(ThreeAddressCode::Label(else_label));

                    // `else` block statements
                    else_block.into_iter().for_each(|stmt| {
                        code_sequence.append(&mut self.visit_statement(stmt).code_sequence);
                    });

                    // if-else block break-out label
                    code_sequence.push(ThreeAddressCode::Label(break_label));

                    CodeObject::builder().code_sequence(code_sequence).build()
                }
                Stmt::For {
                    init: _,
                    condition: _,
                    incr: _,
                    body: _,
                } => todo!(),
            }
        }

        fn visit_expression(&mut self, expr: Expr) -> CodeObject {
            match expr {
                Expr::Id(identifier) => {
                    let result_type = identifier.sym_type.into();

                    let result: BinaryExprOperand = match result_type {
                        ResultType::String => panic!("Invalid operation: String identifier cannot be a part of a Math expression!"),
                        ResultType::Int => IdentI(identifier.id).into(),
                        ResultType::Float => IdentF(identifier.id).into(),
                    };

                    CodeObject::builder()
                        .result(result)
                        .result_type(result_type)
                        .build()
                }
                Expr::IntLiteral(n) => {
                    let temp_result = TempI::new();

                    CodeObject::builder()
                        .result(temp_result.into())
                        .result_type(ResultType::Int)
                        .code_sequence(vec![ThreeAddressCode::StoreI {
                            lhs: LValueI::Temp(temp_result),
                            rhs: n.into(),
                        }])
                        .build()
                }
                Expr::FloatLiteral(n) => {
                    let temp_result = TempF::new();

                    CodeObject::builder()
                        .result(temp_result.into())
                        .result_type(ResultType::Float)
                        .code_sequence(vec![ThreeAddressCode::StoreF {
                            lhs: LValueF::Temp(temp_result),
                            rhs: n.into(),
                        }])
                        .build()
                }
                Expr::Add { op, lhs, rhs } => {
                    let lhs = self.visit_expression(Box::into_inner(lhs));
                    let rhs = self.visit_expression(Box::into_inner(rhs));

                    // The result and result_type of a `CodeObject` returned
                    // by an expression should never be `None`. An expression
                    // should always evaluate to a result with a strong type.
                    let result_type = ThreeAddressCodeVisitor::combined_result_type(
                        lhs.result_type.unwrap(),
                        rhs.result_type.unwrap(),
                    );
                    let (curr_left_operand, mut left_code_seq) =
                        (lhs.result.unwrap(), lhs.code_sequence);
                    let (curr_right_operand, mut right_code_seq) =
                        (rhs.result.unwrap(), rhs.code_sequence);

                    let (curr_code, result_register) = match op {
                        AddOp::Add => match result_type {
                            ResultType::String => unreachable!(),
                            ResultType::Int => {
                                let temp_result = TempI::new();
                                (
                                    ThreeAddressCode::AddI {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                            ResultType::Float => {
                                let temp_result = TempF::new();
                                (
                                    ThreeAddressCode::AddF {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                        },
                        AddOp::Sub => match result_type {
                            ResultType::String => unreachable!(),
                            ResultType::Int => {
                                let temp_result = TempI::new();
                                (
                                    ThreeAddressCode::SubI {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                            ResultType::Float => {
                                let temp_result = TempF::new();
                                (
                                    ThreeAddressCode::SubF {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                        },
                    };

                    left_code_seq.append(&mut right_code_seq);
                    left_code_seq.push(curr_code);

                    CodeObject::builder()
                        .result(result_register)
                        .result_type(result_type)
                        .code_sequence(left_code_seq)
                        .build()
                }
                Expr::Mul { op, lhs, rhs } => {
                    let lhs = self.visit_expression(Box::into_inner(lhs));
                    let rhs = self.visit_expression(Box::into_inner(rhs));

                    // The result and result_type of a `CodeObject` returned
                    // by an expression should never be `None`. An expression
                    // should always evaluate to a result with a strong type.
                    let result_type = ThreeAddressCodeVisitor::combined_result_type(
                        lhs.result_type.unwrap(),
                        rhs.result_type.unwrap(),
                    );
                    let (curr_left_operand, mut left_code_seq) =
                        (lhs.result.unwrap(), lhs.code_sequence);
                    let (curr_right_operand, mut right_code_seq) =
                        (rhs.result.unwrap(), rhs.code_sequence);

                    let (curr_code, result_register) = match op {
                        MulOp::Mul => match result_type {
                            ResultType::String => unreachable!(),
                            ResultType::Int => {
                                let temp_result = TempI::new();
                                (
                                    ThreeAddressCode::MulI {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                            ResultType::Float => {
                                let temp_result = TempF::new();
                                (
                                    ThreeAddressCode::MulF {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                        },
                        MulOp::Div => match result_type {
                            ResultType::String => unreachable!(),
                            ResultType::Int => {
                                let temp_result = TempI::new();
                                (
                                    ThreeAddressCode::DivI {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                            ResultType::Float => {
                                let temp_result = TempF::new();
                                (
                                    ThreeAddressCode::DivF {
                                        lhs: curr_left_operand,
                                        rhs: curr_right_operand,
                                        temp_result,
                                    },
                                    temp_result.into(),
                                )
                            }
                        },
                    };

                    left_code_seq.append(&mut right_code_seq);
                    left_code_seq.push(curr_code);

                    CodeObject::builder()
                        .result(result_register)
                        .result_type(result_type)
                        .code_sequence(left_code_seq)
                        .build()
                }
                Expr::None => {
                    panic!("Invalid AST: AST expression node contains expression variant `None`.")
                }
            }
        }

        fn visit_assignment(&mut self, assigment: Assignment) -> CodeObject {
            let Assignment { lhs, rhs } = assigment;

            let rhs = self.visit_expression(rhs);

            let (curr_operand, mut code_sequence) = (
                // The result of a `CodeObject` returned
                // by an expression should never be `None`.
                // An expression should always evaluate to
                // a result with a strong type.
                rhs.result.unwrap(),
                rhs.code_sequence,
            );

            let assign_code = match lhs.sym_type {
                SymbolType::String => {
                    panic!("Unsupported operation: Cannot ASSIGN to a string identifier!")
                }
                SymbolType::Num(num_type) => match num_type {
                    NumType::Int => ThreeAddressCode::StoreI {
                        lhs: LValueI::Id(IdentI(lhs.id)),
                        rhs: curr_operand,
                    },
                    NumType::Float => ThreeAddressCode::StoreF {
                        lhs: LValueF::Id(IdentF(lhs.id)),
                        rhs: curr_operand,
                    },
                },
            };

            code_sequence.push(assign_code);

            CodeObject::builder().code_sequence(code_sequence).build()
        }

        fn visit_condition(&mut self, condition: Condition) -> CodeObject {
            let Condition { cmp_op, lhs, rhs } = condition;

            let lhs = self.visit_expression(lhs);
            let rhs = self.visit_expression(rhs);
            let (curr_left_operand, mut left_code_seq) = (lhs.result.unwrap(), lhs.code_sequence);
            let (curr_right_operand, mut right_code_seq) = (rhs.result.unwrap(), rhs.code_sequence);

            let else_label = Label::new();

            let curr_code = match cmp_op {
                CmpOp::Lt => Gte {
                    lhs: curr_left_operand,
                    rhs: curr_right_operand,
                    label: else_label,
                },
                CmpOp::Gt => Lte {
                    lhs: curr_left_operand,
                    rhs: curr_right_operand,
                    label: else_label,
                },
                CmpOp::Eq => Ne {
                    lhs: curr_left_operand,
                    rhs: curr_right_operand,
                    label: else_label,
                },
                CmpOp::Ne => Eq {
                    lhs: curr_left_operand,
                    rhs: curr_right_operand,
                    label: else_label,
                },
                CmpOp::Lte => Gt {
                    lhs: curr_left_operand,
                    rhs: curr_right_operand,
                    label: else_label,
                },
                CmpOp::Gte => Lt {
                    lhs: curr_left_operand,
                    rhs: curr_right_operand,
                    label: else_label,
                },
            };

            left_code_seq.append(&mut right_code_seq);
            left_code_seq.push(curr_code);

            CodeObject::builder()
                .jump_to(else_label)
                .code_sequence(left_code_seq)
                .build()
        }
    }
}

#[cfg(test)]
mod test {
    use crate::ast::ast_node::{AddOp, AstNode, Expr, Identifier, MulOp};
    use crate::symbol_table::{NumType, SymbolType};
    use crate::three_addr_code_ir::three_address_code::visit::ThreeAddressCodeVisitor;
    use crate::three_addr_code_ir::ResultType;

    use super::*;

    #[test]
    fn convert_simple_int_expression_ast_to_code_object() {
        // Expression => b*b + a
        // AST -
        //      (+)
        //      / \
        //    (*) (a)
        //   /  \
        // (b)  (b)
        let ast = AstNode::Expr(Expr::Add {
            op: AddOp::Add,
            lhs: Box::new(Expr::Mul {
                op: MulOp::Mul,
                lhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Int),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Int),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                id: "a".to_string(),
                sym_type: SymbolType::Num(NumType::Int),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        let code_object = visitor.walk_ast(ast);

        dbg!(code_object.clone());

        assert!(matches!(
            code_object.result,
            Some(BinaryExprOperand::LValueI(LValueI::Temp(_)))
        ));
        assert_eq!(ResultType::Int, code_object.result_type.unwrap());
        assert_eq!(2, code_object.code_sequence.len());
    }

    #[test]
    fn convert_simple_float_expression_ast_to_code_object() {
        // Expression => b*b + a
        // AST -
        //      (+)
        //      / \
        //    (*) (a)
        //   /  \
        // (b)  (b)
        let ast = AstNode::Expr(Expr::Add {
            op: AddOp::Add,
            lhs: Box::new(Expr::Mul {
                op: MulOp::Mul,
                lhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Float),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Float),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                id: "a".to_string(),
                sym_type: SymbolType::Num(NumType::Float),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        let code_object = visitor.walk_ast(ast);

        dbg!(code_object.clone());

        assert!(matches!(
            code_object.result,
            Some(BinaryExprOperand::LValueF(LValueF::Temp(_)))
        ));
        assert_eq!(ResultType::Float, code_object.result_type.unwrap());
        assert_eq!(2, code_object.code_sequence.len());
    }

    #[test]
    #[should_panic]
    fn convert_math_expression_with_string_identifier_panics() {
        let ast = AstNode::Expr(Expr::Add {
            op: AddOp::Add,
            lhs: Box::new(Expr::Mul {
                op: MulOp::Mul,
                lhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::String,
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Float),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                id: "a".to_string(),
                sym_type: SymbolType::Num(NumType::Float),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        visitor.walk_ast(ast);
    }

    // TODO: This test should not panic after STAGE4
    #[test]
    #[should_panic]
    fn convert_math_expression_with_mixed_num_operand_types_panics() {
        let ast = AstNode::Expr(Expr::Add {
            op: AddOp::Add,
            lhs: Box::new(Expr::Mul {
                op: MulOp::Mul,
                lhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Int),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    id: "b".to_string(),
                    sym_type: SymbolType::Num(NumType::Float),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                id: "a".to_string(),
                sym_type: SymbolType::Num(NumType::Float),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        visitor.walk_ast(ast);
    }
}
