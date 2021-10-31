//! Tiny Assembly - https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use atomic_refcell::AtomicRefCell;
use derive_more::Display;

use crate::symbol_table::{Symbol, SymbolTable};
use crate::three_addr_code_ir::{BinaryExprOperand, LValueF, LValueI, RValue, Temporary};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;

static REGISTER_COUNTER: AtomicU64 = AtomicU64::new(0);

lazy_static::lazy_static! {
    static ref REGISTER_MAP: AtomicRefCell<HashMap<Temporary, Register>> = AtomicRefCell::new(HashMap::new());
}

#[derive(Debug, Copy, Clone, Display)]
#[display(fmt = "r{}", _0)]
pub struct Register(u64);

impl Register {
    pub fn new() -> Self {
        let result = REGISTER_COUNTER.fetch_add(1, Ordering::SeqCst);
        // TODO: Add proper error type
        assert!(result < 200, "Cannot allocate more than 200 registers!");
        Self(result)
    }
}

/// Memory id, stack variable, or a register
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, Display)]
pub enum Opmr {
    Reg(Register),
    Id(String),
}

/// Memory id, stack variable, register or an int literal
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, Display)]
pub enum OpmrIL {
    Literal(i32),
    Location(Opmr),
}

/// Memory id, stack variable, register or a float literal
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, Display)]
pub enum OpmrFL {
    Literal(f64),
    Location(Opmr),
}

/// Memory id, stack variable, register or a number (literal)
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, Display)]
pub enum OpmrL {
    Int(OpmrIL),
    Float(OpmrFL),
}

impl OpmrL {
    fn into_int_opmrl(self) -> OpmrIL {
        match self {
            OpmrL::Int(opmrl) => opmrl,
            _ => panic!("Incorrect OpmrL variant!"),
        }
    }

    fn into_float_opmrl(self) -> OpmrFL {
        match self {
            OpmrL::Float(opmrl) => opmrl,
            _ => panic!("Incorrect OpmrL variant!"),
        }
    }
}

#[derive(Debug, Clone, Display)]
pub struct Target(String);

#[derive(Debug, Clone, Display)]
#[display(fmt = r#"{} "{}""#, id, value)]
pub struct Sid {
    id: String,
    value: String,
}

#[derive(Debug, Display)]
pub enum TinyCode {
    #[display(fmt = "var {}", _0)]
    Var(String),
    #[display(fmt = "str {}", _0)]
    Str(Sid),
    Label(Target),
    #[display(fmt = "move {} {}", _0, _1)]
    Move(OpmrL, Opmr),
    #[display(fmt = "addi {} {}", _0, _1)]
    AddI(OpmrIL, Register),
    #[display(fmt = "subi {} {}", _0, _1)]
    SubI(OpmrIL, Register),
    #[display(fmt = "muli {} {}", _0, _1)]
    MulI(OpmrIL, Register),
    #[display(fmt = "divi {} {}", _0, _1)]
    DivI(OpmrIL, Register),
    #[display(fmt = "addr {} {}", _0, _1)]
    AddF(OpmrFL, Register),
    #[display(fmt = "subr {} {}", _0, _1)]
    SubF(OpmrFL, Register),
    #[display(fmt = "mulr {} {}", _0, _1)]
    MulF(OpmrFL, Register),
    #[display(fmt = "divr {} {}", _0, _1)]
    DivF(OpmrFL, Register),
    #[display(fmt = "inci {}", _0)]
    IncI(Register),
    #[display(fmt = "deci {}", _0)]
    DecI(Register),
    #[display(fmt = "cmpi {} {}", _0, _1)]
    CmpI(OpmrIL, Register),
    #[display(fmt = "cmpr {} {}", _0, _1)]
    CmpF(OpmrFL, Register),
    #[display(fmt = "PUSH - FIXME")]
    Push(Option<OpmrL>),
    #[display(fmt = "POP - FIXME")]
    Pop(Option<Opmr>),
    #[display(fmt = "JSR - FIXME")]
    Jsr(Target),
    #[display(fmt = "RET - FIXME")]
    Ret,
    #[display(fmt = "LINK - FIXME")]
    Link(Option<u32>),
    #[display(fmt = "UNLINK - FIXME")]
    Unlink,
    #[display(fmt = "JMP - FIXME")]
    Jmp(Target),
    #[display(fmt = "JGT - FIXME")]
    Jgt(Target),
    #[display(fmt = "JLT - FIXME")]
    Jlt(Target),
    #[display(fmt = "JGE - FIXME")]
    Jge(Target),
    #[display(fmt = "JLE - FIXME")]
    Jle(Target),
    #[display(fmt = "JEQ - FIXME")]
    Jeq(Target),
    #[display(fmt = "JNE - FIXME")]
    Jne(Target),
    #[display(fmt = "sys readi {}", _0)]
    ReadI(Opmr),
    #[display(fmt = "sys readr {}", _0)]
    ReadF(Opmr),
    #[display(fmt = "sys writei {}", _0)]
    WriteI(Opmr),
    #[display(fmt = "sys writer {}", _0)]
    WriteF(Opmr),
    #[display(fmt = "sys writes {}", _0)]
    WriteS(String),
    #[display(fmt = "sys halt")]
    Halt,
}

impl TinyCode {
    fn process_tac_left_operand(operand: BinaryExprOperand) -> (Register, TinyCode) {
        match operand {
            BinaryExprOperand::LValueI(lval) => match lval {
                LValueI::Temp(temp) => {
                    let existing_reg = *REGISTER_MAP.borrow().get(&temp).unwrap();
                    let new_reg = Register::new();
                    (
                        new_reg,
                        TinyCode::Move(
                            OpmrL::Int(OpmrIL::Location(Opmr::Reg(existing_reg))),
                            Opmr::Reg(new_reg),
                        )
                    )
                }
                LValueI::Id(id) => {
                    let new_reg = Register::new();
                    (
                        new_reg,
                        TinyCode::Move(
                            OpmrL::Int(OpmrIL::Location(Opmr::Id(id.0))),
                            Opmr::Reg(new_reg),
                        )
                    )
                }
            },
            BinaryExprOperand::LValueF(lval) => match lval {
                LValueF::Temp(temp) => {
                    let existing_reg = *REGISTER_MAP.borrow().get(&temp).unwrap();
                    let new_reg = Register::new();
                    (
                        new_reg,
                        TinyCode::Move(
                            OpmrL::Float(OpmrFL::Location(Opmr::Reg(existing_reg))),
                            Opmr::Reg(new_reg),
                        )
                    )
                }
                LValueF::Id(id) => {
                    let new_reg = Register::new();
                    (
                        new_reg,
                        TinyCode::Move(
                            OpmrL::Float(OpmrFL::Location(Opmr::Id(id.0))),
                            Opmr::Reg(new_reg),
                        )
                    )
                }
            },
            BinaryExprOperand::RValue(rval) => {
                match rval {
                    RValue::IntLiteral(n) => {
                        let new_reg = Register::new();
                        (
                            new_reg,
                            TinyCode::Move(
                                OpmrL::Int(OpmrIL::Literal(n)),
                                Opmr::Reg(new_reg),
                            )
                        )
                    }
                    RValue::FloatLiteral(n) => {
                        let new_reg = Register::new();
                        (
                            new_reg,
                            TinyCode::Move(
                                OpmrL::Float(OpmrFL::Literal(n)),
                                Opmr::Reg(new_reg),
                            )
                        )
                    }
                }
            }
        }
    }

    fn process_tac_right_operand(operand: BinaryExprOperand) -> OpmrL {
        match operand {
            BinaryExprOperand::LValueI(lval) => {
                match lval {
                    LValueI::Temp(temp) => {
                        let existing_reg = *REGISTER_MAP.borrow().get(&temp).unwrap();
                        OpmrL::Int(OpmrIL::Location(Opmr::Reg(existing_reg)))
                    }
                    LValueI::Id(id) => OpmrL::Int(OpmrIL::Location(Opmr::Id(id.0)))
                }
            },
            BinaryExprOperand::LValueF(lval) => {
                match lval {
                    LValueF::Temp(temp) => {
                        let existing_reg = *REGISTER_MAP.borrow().get(&temp).unwrap();
                        OpmrL::Float(OpmrFL::Location(Opmr::Reg(existing_reg)))
                    }
                    LValueF::Id(id) => OpmrL::Float(OpmrFL::Location(Opmr::Id(id.0)))
                }
            },
            BinaryExprOperand::RValue(rval) => {
                match rval {
                    RValue::IntLiteral(n) => OpmrL::Int(OpmrIL::Literal(n)),
                    RValue::FloatLiteral(n) => OpmrL::Float(OpmrFL::Literal(n)),
                }
            },
        }
    }
}

#[derive(Debug)]
pub struct TinyCodeSequence {
    pub sequence: Vec<TinyCode>,
}

impl From<ThreeAddressCode> for TinyCodeSequence {
    fn from(three_addr_code: ThreeAddressCode) -> Self {
        match three_addr_code {
            ThreeAddressCode::AddI {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_int_opmrl();
                let result_register = Register::new();
                let add_code = TinyCode::AddI(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, add_code]
                }
            },
            ThreeAddressCode::SubI {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_int_opmrl();
                let result_register = Register::new();
                let sub_code = TinyCode::SubI(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, sub_code]
                }
            },
            ThreeAddressCode::MulI {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_int_opmrl();
                let result_register = Register::new();
                let mul_code = TinyCode::MulI(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, mul_code]
                }
            },
            ThreeAddressCode::DivI {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_int_opmrl();
                let result_register = Register::new();
                let div_code = TinyCode::DivI(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, div_code]
                }
            },
            ThreeAddressCode::StoreI {
                lhs,
                rhs,
            } => {
                let operand1 =  match lhs {
                    LValueI::Temp(temp) => {
                        let maybe_new_register = REGISTER_MAP.borrow()
                            .get(&temp)
                            .copied()
                            .unwrap_or_else(|| Register::new());
                        REGISTER_MAP.borrow_mut().insert(temp, maybe_new_register);
                        Opmr::Reg(maybe_new_register)
                    }
                    LValueI::Id(id) => Opmr::Id(id.0)
                };
                let operand2 = TinyCode::process_tac_right_operand(rhs);
                let move_code = TinyCode::Move(operand2, operand1);

                TinyCodeSequence {
                    sequence: vec![move_code]
                }
            },
            ThreeAddressCode::ReadI {
                identifier
            } => TinyCodeSequence {
                sequence: vec![
                    TinyCode::ReadI(Opmr::Id(identifier.0))
                ]
            },
            ThreeAddressCode::WriteI {
                identifier
            } => TinyCodeSequence {
                sequence: vec![
                    TinyCode::WriteI(Opmr::Id(identifier.0))
                ],
            },
            ThreeAddressCode::AddF {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_float_opmrl();
                let result_register = Register::new();
                let add_code = TinyCode::AddF(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, add_code]
                }
            },
            ThreeAddressCode::SubF {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_float_opmrl();
                let result_register = Register::new();
                let sub_code = TinyCode::SubF(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, sub_code]
                }
            },
            ThreeAddressCode::MulF {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_float_opmrl();
                let result_register = Register::new();
                let mul_code = TinyCode::MulF(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, mul_code]
                }
            }
            ThreeAddressCode::DivF {
                lhs,
                rhs,
                register: temporary
            } => {
                let (operand1, move_code) = TinyCode::process_tac_left_operand(lhs);
                let operand2 = TinyCode::process_tac_right_operand(rhs).into_float_opmrl();
                let result_register = Register::new();
                let div_code = TinyCode::DivF(operand2, operand1);

                REGISTER_MAP.borrow_mut().insert(temporary, result_register);

                TinyCodeSequence {
                    sequence: vec![move_code, div_code]
                }
            },
            ThreeAddressCode::StoreF {
                lhs,
                rhs,
            } => {
                let operand1 =  match lhs {
                    LValueF::Temp(temp) => {
                        let existing_reg = *REGISTER_MAP.borrow().get(&temp).unwrap();
                        Opmr::Reg(existing_reg)
                    }
                    LValueF::Id(id) => Opmr::Id(id.0)
                };
                let operand2 = TinyCode::process_tac_right_operand(rhs);
                let move_code = TinyCode::Move(operand2, operand1);

                TinyCodeSequence {
                    sequence: vec![move_code]
                }
            },
            ThreeAddressCode::ReadF {
                identifier
            } => TinyCodeSequence {
                sequence: vec![
                    TinyCode::ReadF(Opmr::Id(identifier.0))
                ]
            },
            ThreeAddressCode::WriteF {
                identifier
            } => TinyCodeSequence {
                sequence: vec![
                    TinyCode::WriteF(Opmr::Id(identifier.0))
                ],
            },
            ThreeAddressCode::WriteS {
                identifier
            } => TinyCodeSequence {
                sequence: vec![
                    TinyCode::WriteS(identifier.0)
                ],
            },
        }
    }
}

impl From<Vec<ThreeAddressCode>> for TinyCodeSequence {
    fn from(three_adr_code_seq: Vec<ThreeAddressCode>) -> Self {
        // Add all symbol declarations to tiny code sequence
        let symbol_decls = SymbolTable::seal()
            .into_iter()
            .map(|symbol| {
                match symbol {
                    Symbol::String(decl) => {
                        let (name, value) = decl.into_parts();
                        TinyCode::Str(Sid {
                            id: name,
                            value,
                        })
                    },
                    Symbol::Int(decl) => {
                        TinyCode::Var(decl.into_name())
                    },
                    Symbol::Float(decl) => {
                        TinyCode::Var(decl.into_name())
                    },
                }
            })
            .collect();

        let mut result = TinyCodeSequence {
            sequence: symbol_decls
        };

        result.sequence.extend(three_adr_code_seq
            .into_iter()
            .flat_map(|code| Into::<TinyCodeSequence>::into(code).sequence)
        );

        TinyCodeSequence {
            sequence: result.sequence,
        }
    }
}
