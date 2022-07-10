//! Tiny Assembly - https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::symbol_table::symbol::data::{FunctionScopedSymbol, NonFunctionScopedSymbol, Symbol};
use crate::symbol_table::symbol::{data, function};
use crate::symbol_table::SymbolTable;
use crate::three_addr_code_ir;
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{RValueF, RValueI, LValueF, LValueI, TempF, TempI, LValue};
use atomic_refcell::AtomicRefCell;
use std::fmt::Formatter;
use std::rc::Rc;
use crate::register_alloc::types::{RegisterId, RegisterAllocatedThreeAddressCode, SpillType};

#[derive(Debug, Copy, Clone, derive_more::Display)]
#[display(fmt = "label{}", _0)]
pub struct Label(usize);

impl From<three_addr_code_ir::Label> for Label {
    fn from(label: three_addr_code_ir::Label) -> Self {
        Label(label.label())
    }
}

#[derive(Debug, Copy, Clone, derive_more::Display)]
#[display(fmt = "r{}", _0)]
pub struct Register(usize);

impl From<RegisterId> for Register {
    fn from(id: RegisterId) -> Self {
        Register(id.into_inner())
    }
}

/// Memory id, stack variable, or a register
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone)]
pub enum Opmr {
    Reg(Register),
    Id(data::Symbol),
}

// Using hand written impl for display for Opmr
// because we need to name the function scoped symbols,
// i.e., function parameters and local variables,
// as positive/negative offsets to the frame pointer.
impl std::fmt::Display for Opmr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Opmr::Reg(register) => {
                write!(f, "{}", register)
            }
            Opmr::Id(id) => {
                match id {
                    Symbol::NonFunctionScopedSymbol(symbol) => {
                        write!(f, "{}", symbol)
                    }
                    Symbol::FunctionScopedSymbol(symbol) => {
                        match **symbol {
                            data::FunctionScopedSymbol::Int {
                                symbol_type: data::FunctionScopedSymbolType::Parameter(num_params),
                                index,
                            }
                            | data::FunctionScopedSymbol::Float {
                                symbol_type: data::FunctionScopedSymbolType::Parameter(num_params),
                                index,
                            } => {
                                write!(
                                    f,
                                    "${}",
                                    num_params - index + 1 + 1 /* for return address block on stack */
                                )
                            }
                            data::FunctionScopedSymbol::Int { index, .. }
                            | data::FunctionScopedSymbol::Float { index, .. } => {
                                write!(f, "$-{}", index)
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Memory id, stack variable, register or an int literal
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, derive_more::Display)]
pub enum OpmrIL {
    Literal(i32),
    Location(Opmr),
}

/// Memory id, stack variable, register or a float literal
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, derive_more::Display)]
pub enum OpmrFL {
    Literal(f64),
    Location(Opmr),
}

/// Memory id, stack variable, register or a number (literal)
/// https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt
#[derive(Debug, Clone, derive_more::Display)]
pub enum OpmrL {
    Int(OpmrIL),
    Float(OpmrFL),
}

#[derive(Debug, Clone, Default, derive_more::Display)]
#[display(fmt = "{} {}", id, value)]
pub struct Sid {
    id: String,
    value: String,
}

#[allow(unused)]
#[derive(Debug, derive_more::Display)]
pub enum TinyCode {
    #[display(fmt = "var {}", _0)]
    Var(String),
    #[display(fmt = "str {}", _0)]
    Str(Sid),
    #[display(fmt = "label {}", _0)]
    Label(Label),
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
    #[display(fmt = "jmp {}", _0)]
    Jmp(Label),
    #[display(fmt = "jgt {}", _0)]
    Jgt(Label),
    #[display(fmt = "jlt {}", _0)]
    Jlt(Label),
    #[display(fmt = "jge {}", _0)]
    Jge(Label),
    #[display(fmt = "jle {}", _0)]
    Jle(Label),
    #[display(fmt = "jeq {}", _0)]
    Jeq(Label),
    #[display(fmt = "jne {}", _0)]
    Jne(Label),
    #[display(fmt = "sys readi {}", _0)]
    ReadI(Opmr),
    #[display(fmt = "sys readr {}", _0)]
    ReadF(Opmr),
    #[display(fmt = "sys writei {}", _0)]
    WriteI(Opmr),
    #[display(fmt = "sys writer {}", _0)]
    WriteF(Opmr),
    #[display(fmt = "sys writes {}", _0)]
    WriteS(data::Symbol),
    #[display(fmt = "push")]
    PushEmpty,
    #[display(fmt = "push {}", _0)]
    Push(OpmrL),
    #[display(fmt = "pop")]
    PopEmpty,
    #[display(fmt = "pop {}", _0)]
    Pop(Opmr),
    #[display(fmt = "label {}", "_0.name()")]
    FunctionLabel(Rc<function::Symbol>),
    #[display(fmt = "jsr {}", "_0.name()")]
    Jsr(Rc<function::Symbol>),
    #[display(fmt = "ret")]
    Ret,
    #[display(fmt = "link")]
    LinkEmpty,
    #[display(fmt = "link {}", _0)]
    Link(usize),
    #[display(fmt = "unlnk")]
    Unlink,
    #[display(fmt = "sys halt")]
    Halt,
    #[display(fmt = "end")]
    End,
}

#[derive(Debug, Default)]
pub struct TinyCodeSequence {
    pub sequence: Vec<TinyCode>,
}

impl From<RegisterAllocatedThreeAddressCode> for TinyCodeSequence {
    fn from(reg_alloc_tac: RegisterAllocatedThreeAddressCode) -> Self {
        let mut code_sequence = vec![];
        let (tac, register_allocations, spills) = reg_alloc_tac.into_parts();
        // Generate LOAD/STORE spill code for this 3AC
        spills.into_iter().for_each(|spill| {
            let (spill_type, register_id, memory_location) = spill.into_parts();
            match spill_type {
                // Move from memory location to register
                SpillType::Load => {
                    code_sequence.push(TinyCode::Move(
                        OpmrL::Int(OpmrIL::Location(Opmr::Id(memory_location))),
                        Opmr::Reg(register_id.into()),
                    ));
                }
                // Move from register to memory location
                SpillType::Store => {
                    code_sequence.push(TinyCode::Move(
                        OpmrL::Int(OpmrIL::Location(Opmr::Reg(register_id.into()))),
                        Opmr::Id(memory_location),
                    ));
                }
            }
        });

        // Generate tiny code for this 3AC
        match tac {
            ThreeAddressCode::AddI {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move `lhs_reg` to `result_reg`
                code_sequence.push(TinyCode::Move(
                    OpmrL::Int(OpmrIL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::AddI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::SubI {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move `lhs_reg` to `result_reg`
                code_sequence.push(TinyCode::Move(
                    OpmrL::Int(OpmrIL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::SubI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::MulI {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move `lhs_reg` to `result_reg`
                code_sequence.push(TinyCode::Move(
                    OpmrL::Int(OpmrIL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::MulI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::DivI {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move `lhs_reg` to `result_reg`
                code_sequence.push(TinyCode::Move(
                   OpmrL::Int(OpmrIL::Location(Opmr::Reg(lhs_reg))),
                   Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::DivI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::AddF {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move lhs_reg to result_reg
                code_sequence.push(TinyCode::Move(
                    OpmrL::Float(OpmrFL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::AddF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::SubF {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move lhs_reg to result_reg
                code_sequence.push(TinyCode::Move(
                    OpmrL::Float(OpmrFL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::SubF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::MulF {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move lhs_reg to result_reg
                code_sequence.push(TinyCode::Move(
                    OpmrL::Float(OpmrFL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::MulF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::DivF {
                lhs,
                rhs,
                temp_result
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();
                let result_reg = register_allocations[&temp_result.into()].into();

                // Move lhs_reg to result_reg
                code_sequence.push(TinyCode::Move(
                    OpmrL::Float(OpmrFL::Location(Opmr::Reg(lhs_reg))),
                    Opmr::Reg(result_reg)
                ));

                // Generate tiny code for the op
                code_sequence.push(TinyCode::DivF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    result_reg
                ));
            }
            ThreeAddressCode::StoreI {
                lhs,
                rhs
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();

                // Generate tiny code for the 3AC
                match rhs {
                    RValueI::RValue(n) => {
                        code_sequence.push(TinyCode::Move(
                            OpmrL::Int(OpmrIL::Literal(n)),
                            Opmr::Reg(lhs_reg)
                        ));
                    }
                    RValueI::LValue(lvalue) => {
                        let rhs_reg = register_allocations[&lvalue.into()].into();

                        code_sequence.push(TinyCode::Move(
                            OpmrL::Int(OpmrIL::Location(Opmr::Reg(rhs_reg))),
                            Opmr::Reg(lhs_reg)
                        ));
                    }
                }
            }
            ThreeAddressCode::ReadI {
                identifier
            } => {
                let ident_reg = register_allocations[&identifier.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::ReadI(Opmr::Reg(ident_reg)));
            }
            ThreeAddressCode::WriteI {
                identifier
            } => {
                let ident_reg = register_allocations[&identifier.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::WriteI(Opmr::Reg(ident_reg)));
            }
            ThreeAddressCode::StoreF {
                lhs,
                rhs
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();

                // Generate tiny code for the 3AC
                match rhs {
                    RValueF::RValue(n) => {
                        code_sequence.push(TinyCode::Move(
                            OpmrL::Float(OpmrFL::Literal(n)),
                            Opmr::Reg(lhs_reg)
                        ));
                    }
                    RValueF::LValue(lvalue) => {
                        let rhs_reg = register_allocations[&lvalue.into()].into();

                        code_sequence.push(TinyCode::Move(
                            OpmrL::Float(OpmrFL::Location(Opmr::Reg(rhs_reg))),
                            Opmr::Reg(lhs_reg)
                        ));
                    }
                }
            }
            ThreeAddressCode::ReadF {
                identifier
            } => {
                let ident_reg = register_allocations[&identifier.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::ReadF(Opmr::Reg(ident_reg)));
            }
            ThreeAddressCode::WriteF {
                identifier
            } => {
                let ident_reg = register_allocations[&identifier.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::WriteF(Opmr::Reg(ident_reg)));
            }
            ThreeAddressCode::WriteS {
                identifier
            } => {
                code_sequence.push(TinyCode::WriteS(identifier.0));
            }
            ThreeAddressCode::Label(label) => {
                code_sequence.push(TinyCode::Label(label.into()));
            }
            ThreeAddressCode::Jump(label) => {
                code_sequence.push(TinyCode::Jmp(label.into()));
            }
            ThreeAddressCode::GtI {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jgt(label.into()));
            }
            ThreeAddressCode::LtI {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jlt(label.into()));
            }
            ThreeAddressCode::GteI {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jge(label.into()));
            }
            ThreeAddressCode::LteI {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jle(label.into()));
            }
            ThreeAddressCode::NeI {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jne(label.into()));
            }
            ThreeAddressCode::EqI {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpI(
                    OpmrIL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jeq(label.into()));
            }
            ThreeAddressCode::GtF {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jgt(label.into()));
            }
            ThreeAddressCode::LtF {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jlt(label.into()));
            }
            ThreeAddressCode::GteF {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jge(label.into()));
            }
            ThreeAddressCode::LteF {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jle(label.into()));
            }
            ThreeAddressCode::NeF {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jne(label.into()));
            }
            ThreeAddressCode::EqF {
                lhs,
                rhs,
                label
            } => {
                let lhs_reg = register_allocations[&lhs.into()].into();
                let rhs_reg = register_allocations[&rhs.into()].into();

                // Generate tiny code for the 3AC
                code_sequence.push(TinyCode::CmpF(
                    OpmrFL::Location(Opmr::Reg(rhs_reg)),
                    lhs_reg
                ));

                code_sequence.push(TinyCode::Jeq(label.into()));
            }
            ThreeAddressCode::FunctionLabel(func) => {
                code_sequence.push(TinyCode::FunctionLabel(func.0))
            }
            ThreeAddressCode::Jsr(func) => {
                code_sequence.push(TinyCode::Jsr(func.0))
            }
            ThreeAddressCode::Link(func) => {
                let num_locals = func.num_locals();
                if num_locals > 0 {
                    code_sequence.push(TinyCode::Link(num_locals));
                } else {
                    code_sequence.push(TinyCode::LinkEmpty);
                }
            }
            ThreeAddressCode::Ret => {
                code_sequence.push(TinyCode::Unlink);
                code_sequence.push(TinyCode::Ret);
            }
            ThreeAddressCode::PushEmpty => {
                code_sequence.push(TinyCode::PushEmpty);
            }
            ThreeAddressCode::PushI(lvalue) => {
                let reg = register_allocations[&lvalue.into()].into();
                code_sequence.push(TinyCode::Push(OpmrL::Int(OpmrIL::Location(Opmr::Reg(reg)))));
            }
            ThreeAddressCode::PushF(lvalue) => {
                let reg = register_allocations[&lvalue.into()].into();
                code_sequence.push(TinyCode::Push(OpmrL::Float(OpmrFL::Location(Opmr::Reg(reg)))));
            }
            ThreeAddressCode::PopEmpty => {
                code_sequence.push(TinyCode::PopEmpty);
            }
            ThreeAddressCode::PopI(lvalue) => {
                let reg = register_allocations[&lvalue.into()].into();
                code_sequence.push(TinyCode::Pop(Opmr::Reg(reg)));
            }
            ThreeAddressCode::PopF(lvalue) => {
                let reg = register_allocations[&lvalue.into()].into();
                code_sequence.push(TinyCode::Pop(Opmr::Reg(reg)));
            }
        }

        TinyCodeSequence {
            sequence: code_sequence,
        }
    }
}

impl From<Vec<RegisterAllocatedThreeAddressCode>> for TinyCodeSequence {
    fn from(three_adr_code_seq: Vec<RegisterAllocatedThreeAddressCode>) -> Self {
        // Add all symbol declarations to tiny code sequence
        let symbol_decls = SymbolTable::global_symbols()
            .into_iter()
            .map(|symbol| match &*symbol {
                NonFunctionScopedSymbol::String { name, value } => TinyCode::Str(Sid {
                    id: name.clone(),
                    value: value.clone(),
                }),
                NonFunctionScopedSymbol::Int { name } => TinyCode::Var(name.clone()),
                NonFunctionScopedSymbol::Float { name } => TinyCode::Var(name.clone()),
            })
            .collect();

        let mut result = TinyCodeSequence {
            sequence: symbol_decls,
        };

        // Insert empty slot for result of `main` and then a
        // call to `main` itself.
        let main_func_symbol =
            SymbolTable::function_symbol_for_name("main").expect("No `main` function found!");
        result.sequence.push(TinyCode::PushEmpty);
        result.sequence.push(TinyCode::Jsr(main_func_symbol));
        result.sequence.push(TinyCode::Halt);

        result.sequence.extend(
            three_adr_code_seq
                .into_iter()
                .flat_map(|code| Into::<TinyCodeSequence>::into(code).sequence),
        );

        result.sequence.push(TinyCode::End);

        result
    }
}
