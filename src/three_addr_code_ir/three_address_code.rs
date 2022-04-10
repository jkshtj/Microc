use crate::three_addr_code_ir::{BinaryExprOperand, IdentF, IdentI, IdentS, LValueF, LValueI, Label, ResultType, TempF, TempI, FunctionIdent};

#[derive(Debug, Clone, derive_more::Display)]
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
    GtI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LT {} {} {}", lhs, rhs, label)]
    LtI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "GE {} {} {}", lhs, rhs, label)]
    GteI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LE {} {} {}", lhs, rhs, label)]
    LteI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "NE {} {} {}", lhs, rhs, label)]
    NeI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "EQ {} {} {}", lhs, rhs, label)]
    EqI {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "GT {} {} {}", lhs, rhs, label)]
    GtF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LT {} {} {}", lhs, rhs, label)]
    LtF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "GE {} {} {}", lhs, rhs, label)]
    GteF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LE {} {} {}", lhs, rhs, label)]
    LteF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "NE {} {} {}", lhs, rhs, label)]
    NeF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "EQ {} {} {}", lhs, rhs, label)]
    EqF {
        lhs: BinaryExprOperand,
        rhs: BinaryExprOperand,
        label: Label,
    },
    #[display(fmt = "LABEL {}", "_0.name()")]
    FunctionLabel(FunctionIdent),
    #[display(fmt = "JSR {}", "_0.name()")]
    Jsr(FunctionIdent),
    #[display(fmt = "LINK")]
    Link(FunctionIdent),
    #[display(fmt = "RET")]
    Ret,
    #[display(fmt = "PUSH")]
    PushEmpty,
    #[display(fmt = "PUSH {}", _0)]
    Push(BinaryExprOperand),
    #[display(fmt = "POP")]
    PopEmpty,
    #[display(fmt = "POP {}", _0)]
    PopI(LValueI),
    #[display(fmt = "POP {}", _0)]
    PopF(LValueF),
    #[display(fmt = "STOREI {} $R", _0)]
    StoreFuncReturnValI(BinaryExprOperand),
    #[display(fmt = "STOREF {} $R", _0)]
    StoreFuncReturnValF(BinaryExprOperand),
}

// TODO: Factor out all type checking into its own visitor.
pub mod visit {
    use crate::ast::ast_node::visit::Visitor;
    use crate::ast::ast_node::{
        AddOp, Assignment, AstNode, CmpOp, Condition, Expr, Item, MulOp, Stmt,
    };
    use crate::symbol_table::symbol::data::DataType;
    use crate::symbol_table::symbol::{NumType, function};
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode::{
        EqF, EqI, GtF, GtI, GteF, GteI, Jump, LtF, LtI, LteF, LteI, NeF, NeI,
    };
    use crate::three_addr_code_ir::{BinaryExprOperand, IdentF, IdentI, LValueF, LValueI, Label, ResultType, TempF, TempI, FunctionIdent, reset_temp_counter};
    use typed_builder::TypedBuilder;
    use crate::symbol_table::symbol::function::ReturnType;

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
                AstNode::Item(item) => self.visit_item(item),
            }
        }
    }

    // Note - Visitor pattern does not care about traversal strategy. For instance I can
    //  traverse the AST using Pre-Order traversal and the visitor pattern will still apply.
    //  In fact, if my visitor did not have to return a value from each visit_* call, I could
    //  have separated the traversal strategy into a separate method.
    // TODO: Can the Post-Order traversal of the AST be done iteratively?
    impl Visitor<CodeObject> for ThreeAddressCodeVisitor {
        fn visit_item(&mut self, item: Item) -> CodeObject {
            match item {
                // TODO: Implement unit tests for 3AC code gen for functions
                Item::Function { symbol, body } => {
                    reset_temp_counter();
                    let mut code_sequence = vec![];
                    code_sequence.push(ThreeAddressCode::FunctionLabel(FunctionIdent(symbol.clone())));
                    code_sequence.push(ThreeAddressCode::Link(FunctionIdent(symbol.clone())));
                    let mut func_body = body
                        .into_iter()
                        .flat_map(|stmt| self.visit_statement(stmt).code_sequence)
                        .collect();
                    code_sequence.append(&mut func_body);

                    CodeObject::builder().code_sequence(code_sequence).build()
                }
            }
        }

        fn visit_statement(&mut self, stmt: Stmt) -> CodeObject {
            match stmt {
                Stmt::Read(identifiers) => {
                    let code_sequence = identifiers
                        .into_iter()
                        .map(|identifier| match identifier.data_type() {
                            DataType::String => {
                                panic!("Unsupported operation: cannot READ into string identifier!")
                            }
                            DataType::Num(num_type) => match num_type {
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
                        .map(|identifier| match identifier.data_type() {
                            DataType::String => ThreeAddressCode::WriteS {
                                identifier: identifier.into(),
                            },
                            DataType::Num(num_type) => match num_type {
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
                    if !else_block.is_empty() {
                        else_block.into_iter().for_each(|stmt| {
                            code_sequence.append(&mut self.visit_statement(stmt).code_sequence);
                        });

                        // Jump to break_label
                        code_sequence.push(Jump(break_label));
                    }

                    // if-else block break-out label
                    code_sequence.push(ThreeAddressCode::Label(break_label));

                    CodeObject::builder().code_sequence(code_sequence).build()
                }
                Stmt::For {
                    init,
                    condition,
                    incr,
                    body,
                } => {
                    // Generate loop init 3AC
                    let mut code_sequence = init.map_or(vec![], |assignment| {
                        self.visit_assignment(assignment).code_sequence
                    });
                    let loop_start_label = Label::new();
                    code_sequence.push(ThreeAddressCode::Label(loop_start_label));

                    // Generate loop condition 3AC
                    let mut condition = self.visit_condition(condition);
                    code_sequence.append(&mut condition.code_sequence);
                    // Unwrapping is safe here as the `jump_to` field
                    // of the returned `CodeObject`, from visiting a `Condition`
                    // is guaranteed to be set.
                    let loop_break_label = condition.jump_to.unwrap();

                    // Generate loop incr 3AC
                    let loop_incr_label = Label::new();
                    let mut incr_statements = incr.map_or(vec![], |assignment| {
                        self.visit_assignment(assignment).code_sequence
                    });

                    // Add loop statements 3AC
                    body.into_iter().for_each(|stmt| {
                        code_sequence.append(&mut self.visit_statement(stmt).code_sequence);
                    });

                    // Add loop incr 3AC
                    code_sequence.push(ThreeAddressCode::Label(loop_incr_label));
                    code_sequence.append(&mut incr_statements);
                    code_sequence.push(ThreeAddressCode::Jump(loop_start_label));

                    // loop break-out label
                    code_sequence.push(ThreeAddressCode::Label(loop_break_label));

                    CodeObject::builder().code_sequence(code_sequence).build()
                }
                Stmt::Return(expr) => {
                    let mut code_sequence = vec![];
                    let mut expr_code_object = self.visit_expression(expr);
                    code_sequence.append(&mut expr_code_object.code_sequence);

                    // TODO: For call expressions the result can indeed be null. This
                    // makes unwrapping the `result` field of expressions panic-prone
                    // and unsafe, which we are doing at numerous places right now.
                    if let CodeObject {
                        result: Some(result),
                        result_type: Some(result_type),
                        ..
                    } = expr_code_object {
                        match result_type {
                            ResultType::Int => code_sequence.push(ThreeAddressCode::StoreFuncReturnValI(result)),
                            ResultType::Float => code_sequence.push(ThreeAddressCode::StoreFuncReturnValF(result)),
                        }
                    }

                    code_sequence.push(ThreeAddressCode::Ret);

                    CodeObject::builder()
                        .code_sequence(code_sequence)
                        .build()
                },
                Stmt::None => {
                    panic!("Invalid AST: AST statement node contains statement variant `None`.")
                },
            }
        }

        fn visit_expression(&mut self, expr: Expr) -> CodeObject {
            match expr {
                Expr::Id(identifier) => {
                    let result_type = identifier.data_type().into();

                    let result: BinaryExprOperand = match result_type {
                        ResultType::Int => IdentI(identifier.symbol).into(),
                        ResultType::Float => IdentF(identifier.symbol).into(),
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
                Expr::Call { func_symbol, args } => {
                    let mut code_sequence = vec![];
                    let return_type = func_symbol.return_type();

                    // Generate instructions to evaluate all function
                    // parameters and add them to the existing code sequence.
                    // Store the temporaries containing the results of the function
                    // parameter expressions to set up the stack in preparation
                    // for the function call.
                    let num_args = args.len();
                    let mut push_arg_instrs = args
                        .into_iter()
                        .map(|expr| {
                            let mut expr_code_obj = self.visit_expression(expr);
                            code_sequence.append(&mut expr_code_obj.code_sequence);
                            // The result of a `CodeObject` returned
                            // by an expression should never be `None`.
                            // An expression should always evaluate to
                            // a result with a strong type.
                            expr_code_obj.result.unwrap()
                        })
                        .map(|arg| ThreeAddressCode::Push(arg))
                        .collect();

                    // If the function being called returns a value,
                    // push empty slot for result of function.
                    if return_type != function::ReturnType::Void {
                        code_sequence.push(ThreeAddressCode::PushEmpty);
                    }

                    code_sequence.append(&mut push_arg_instrs);

                    // Jump to target - current pc is pushed onto the stack as part of this instruction.
                    // The pc pushed onto the stack should be popped off in the callee code.
                    code_sequence.push(ThreeAddressCode::Jsr(FunctionIdent(func_symbol.clone())));

                    // Pop all the function parameters
                    (0..num_args).for_each(|_| code_sequence.push(ThreeAddressCode::PopEmpty));

                    // If the function being called returns a value,
                    // pop the function call result and store it in a temporary.
                    let (result_register, result_type) = match return_type {
                        ReturnType::Num(num_type) => match num_type {
                            NumType::Int => {
                                let result_register = TempI::new();
                                code_sequence.push(ThreeAddressCode::PopI(LValueI::Temp(result_register)));
                                (Some(result_register.into()), Some(ResultType::Int))
                            },
                            NumType::Float => {
                                let result_register = TempF::new();
                                code_sequence.push(ThreeAddressCode::PopF(LValueF::Temp(result_register)));
                                (Some(result_register.into()), Some(ResultType::Float))
                            },
                        },
                        ReturnType::Void => (None, None),
                    };

                    match return_type {
                        ReturnType::Num(_) => CodeObject::builder()
                            .result(result_register.unwrap())
                            .result_type(result_type.unwrap())
                            .code_sequence(code_sequence)
                            .build(),
                        ReturnType::Void => CodeObject::builder()
                            .code_sequence(code_sequence)
                            .build(),
                    }
                },
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

            let assign_code = match lhs.data_type() {
                DataType::String => {
                    panic!("Unsupported operation: Cannot ASSIGN to a string identifier!")
                }
                DataType::Num(num_type) => match num_type {
                    NumType::Int => ThreeAddressCode::StoreI {
                        lhs: LValueI::Id(IdentI(lhs.symbol)),
                        rhs: curr_operand,
                    },
                    NumType::Float => ThreeAddressCode::StoreF {
                        lhs: LValueF::Id(IdentF(lhs.symbol)),
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
            // The result and result_type of a `CodeObject` returned
            // by an expression should never be `None`. An expression
            // should always evaluate to a result with a strong type.
            let (left_result_type, right_result_type) =
                (lhs.result_type.unwrap(), rhs.result_type.unwrap());
            let (curr_left_operand, mut left_code_seq) = (lhs.result.unwrap(), lhs.code_sequence);
            let (curr_right_operand, mut right_code_seq) = (rhs.result.unwrap(), rhs.code_sequence);

            let comparison_type =
                ThreeAddressCodeVisitor::combined_result_type(left_result_type, right_result_type);

            let else_label = Label::new();

            let curr_code = match cmp_op {
                CmpOp::Lt => match comparison_type {
                    ResultType::Int => GteI {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                    ResultType::Float => GteF {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                },
                CmpOp::Gt => match comparison_type {
                    ResultType::Int => LteI {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                    ResultType::Float => LteF {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                },
                CmpOp::Eq => match comparison_type {
                    ResultType::Int => NeI {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                    ResultType::Float => NeF {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                },
                CmpOp::Ne => match comparison_type {
                    ResultType::Int => EqI {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                    ResultType::Float => EqF {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                },
                CmpOp::Lte => match comparison_type {
                    ResultType::Int => GtI {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                    ResultType::Float => GtF {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                },
                CmpOp::Gte => match comparison_type {
                    ResultType::Int => LtI {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
                    ResultType::Float => LtF {
                        lhs: curr_left_operand,
                        rhs: curr_right_operand,
                        label: else_label,
                    },
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
    use crate::ast::ast_node::{AddOp, AstNode, CmpOp, Condition, Expr, Identifier, MulOp};
    use crate::three_addr_code_ir::three_address_code::visit::ThreeAddressCodeVisitor;
    use crate::three_addr_code_ir::ResultType;

    use super::*;
    use crate::ast::ast_node;
    use crate::ast::ast_node::AstNode::Stmt;
    use crate::symbol_table::symbol::data;
    use crate::symbol_table::symbol::NumType;
    use std::rc::Rc;

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
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Int {
                        name: "b".to_string(),
                    })),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Int {
                        name: "b".to_string(),
                    })),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Int {
                    name: "a".to_string(),
                })),
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
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                        name: "b".to_string(),
                    })),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                        name: "b".to_string(),
                    })),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                    name: "a".to_string(),
                })),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        let code_object = visitor.walk_ast(ast);

        dbg!(code_object.clone());

        matches!(
            code_object.result,
            Some(BinaryExprOperand::LValueF(LValueF::Temp(_)))
        );
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
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::String {
                        name: "b".to_string(),
                        value: "value".to_string(),
                    })),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                        name: "b".to_string(),
                    })),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                    name: "a".to_string(),
                })),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        visitor.walk_ast(ast);
    }

    #[test]
    #[should_panic]
    fn convert_condition_comparing_string_identifier_panics() {
        let ast = AstNode::Stmt(ast_node::Stmt::If {
            condition: Condition {
                cmp_op: CmpOp::Lt,
                lhs: Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::String {
                        name: "b".to_string(),
                        value: "value".to_string(),
                    })),
                }),
                rhs: Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::String {
                        name: "b".to_string(),
                        value: "value".to_string(),
                    })),
                }),
            },
            then_block: vec![],
            else_block: vec![],
        });

        let mut visitor = ThreeAddressCodeVisitor;

        visitor.walk_ast(ast);
    }

    // TODO: This test should not panic after STAGE5
    #[test]
    #[should_panic]
    fn convert_math_expression_with_mixed_num_operand_types_panics() {
        let ast = AstNode::Expr(Expr::Add {
            op: AddOp::Add,
            lhs: Box::new(Expr::Mul {
                op: MulOp::Mul,
                lhs: Box::new(Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Int {
                        name: "b".to_string(),
                    })),
                })),
                rhs: Box::new(Expr::Id(Identifier {
                    symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                        name: "b".to_string(),
                    })),
                })),
            }),
            rhs: Box::new(Expr::Id(Identifier {
                symbol: data::Symbol::NonFunctionScopedSymbol(Rc::new(data::NonFunctionScopedSymbol::Float {
                    name: "a".to_string(),
                })),
            })),
        });

        let mut visitor = ThreeAddressCodeVisitor;

        visitor.walk_ast(ast);
    }
}
