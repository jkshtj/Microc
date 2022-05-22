use linked_hash_map::LinkedHashMap;
use crate::cfg::basic_block::{BBLabel, ImmutableBasicBlock};
use crate::three_addr_code_ir::{LValueI, LValueF, LValue, BinaryExprOperandI, BinaryExprOperandF, IdentI, IdentF};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use std::collections::HashSet;
use crate::cfg::ControlFlowGraph;
use crate::symbol_table::SymbolTable;
use crate::symbol_table::symbol::data::DataType;
use crate::symbol_table::symbol::{NumType, data};
use std::fmt::{Display, Formatter};

/// ThreeAddressCode nodes containing GEN and KILL
/// sets for the current 3AC node.
#[derive(Debug, PartialEq)]
pub struct GenKillDecoratedThreeAddressCode {
    tac: ThreeAddressCode,
    gen: HashSet<LValue>,
    kill: HashSet<LValue>,
}

impl GenKillDecoratedThreeAddressCode {
    pub fn gen(&self) -> impl Iterator<Item=&LValue> {
        self.gen.iter()
    }

    pub fn kill(&self) -> impl Iterator<Item=&LValue> {
        self.kill.iter()
    }

    pub fn tac(&self) -> &ThreeAddressCode {
        &self.tac
    }
}

impl From<ThreeAddressCode> for GenKillDecoratedThreeAddressCode {
    fn from(tac: ThreeAddressCode) -> Self {
        let mut gen = HashSet::new();
        let mut kill = HashSet::new();

        match &tac {
            ThreeAddressCode::AddI { lhs, rhs, temp_result } |
            ThreeAddressCode::SubI { lhs, rhs, temp_result } |
            ThreeAddressCode::MulI { lhs, rhs, temp_result } |
            ThreeAddressCode::DivI { lhs, rhs, temp_result } => {
                if let BinaryExprOperandI::LValue(lvalue) = lhs {
                    gen.insert(LValue::LValueI(lvalue.clone()));
                }

                if let BinaryExprOperandI::LValue(lvalue) = rhs {
                    gen.insert(LValue::LValueI(lvalue.clone()));
                }

                kill.insert((*temp_result).into());
            },
            ThreeAddressCode::StoreI { lhs, rhs} => {
                if let BinaryExprOperandI::LValue(lvalue) = rhs {
                    gen.insert(LValue::LValueI(lvalue.clone()));
                }

                kill.insert(LValue::LValueI(lhs.clone()));
            }
            ThreeAddressCode::ReadI { identifier } => {
                kill.insert(LValue::LValueI(LValueI::Id(identifier.clone())));
            }
            ThreeAddressCode::WriteI { identifier } => {
                gen.insert(LValue::LValueI(LValueI::Id(identifier.clone())));
            }
            ThreeAddressCode::AddF { lhs, rhs, temp_result } |
            ThreeAddressCode::SubF { lhs, rhs, temp_result } |
            ThreeAddressCode::MulF { lhs, rhs, temp_result } |
            ThreeAddressCode::DivF { lhs, rhs, temp_result } => {
                if let BinaryExprOperandF::LValue(lvalue) = lhs {
                    gen.insert(LValue::LValueF(lvalue.clone()));
                }

                if let BinaryExprOperandF::LValue(lvalue) = rhs {
                    gen.insert(LValue::LValueF(lvalue.clone()));
                }

                kill.insert((*temp_result).into());
            }
            ThreeAddressCode::StoreF { lhs, rhs } => {
                if let BinaryExprOperandF::LValue(lvalue) = rhs {
                    gen.insert(LValue::LValueF(lvalue.clone()));
                }

                kill.insert(LValue::LValueF(lhs.clone()));
            }
            ThreeAddressCode::ReadF { identifier } => {
                kill.insert(LValue::LValueF(LValueF::Id(identifier.clone())));
            }
            ThreeAddressCode::WriteF { identifier } => {
                gen.insert(LValue::LValueF(LValueF::Id(identifier.clone())));
            }
            ThreeAddressCode::GtI { lhs, rhs, .. } |
            ThreeAddressCode::LtI { lhs, rhs, .. } |
            ThreeAddressCode::GteI { lhs, rhs, .. } |
            ThreeAddressCode::LteI { lhs, rhs, .. } |
            ThreeAddressCode::NeI { lhs, rhs, .. } |
            ThreeAddressCode::EqI { lhs, rhs, .. } => {
                if let BinaryExprOperandI::LValue(lvalue) = lhs {
                    gen.insert(LValue::LValueI(lvalue.clone()));
                }

                if let BinaryExprOperandI::LValue(lvalue) = rhs {
                    gen.insert(LValue::LValueI(lvalue.clone()));
                }
            }
            ThreeAddressCode::GtF { lhs, rhs, .. } |
            ThreeAddressCode::LtF { lhs, rhs, .. } |
            ThreeAddressCode::GteF { lhs, rhs, .. } |
            ThreeAddressCode::LteF { lhs, rhs, .. } |
            ThreeAddressCode::NeF { lhs, rhs, .. } |
            ThreeAddressCode::EqF { lhs, rhs, .. } => {
                if let BinaryExprOperandF::LValue(lvalue) = lhs {
                    gen.insert(LValue::LValueF(lvalue.clone()));
                }

                if let BinaryExprOperandF::LValue(lvalue) = rhs {
                    gen.insert(LValue::LValueF(lvalue.clone()));
                }
            }
            ThreeAddressCode::PushI(op) => {
                if let BinaryExprOperandI::LValue(lvalue) = op {
                    gen.insert(LValue::LValueI(lvalue.clone()));
                }
            }
            ThreeAddressCode::PushF(op) => {
                if let BinaryExprOperandF::LValue(lvalue) = op {
                    gen.insert(LValue::LValueF(lvalue.clone()));
                }
            }
            ThreeAddressCode::PopI(op) => {
                kill.insert(LValue::LValueI(op.clone()));
            }
            ThreeAddressCode::PopF(op) => {
                kill.insert(LValue::LValueF(op.clone()));
            }
            ThreeAddressCode::Jsr(_) => {
                SymbolTable::global_symbols()
                    .into_iter()
                    .filter_map(|symbol| match symbol.data_type() {
                        DataType::Num(NumType::Int) => Some(LValue::LValueI(LValueI::Id(IdentI(symbol.into())))),
                        DataType::Num(NumType::Float) => Some(LValue::LValueF(LValueF::Id(IdentF(symbol.into())))),
                        _ => None
                    })
                    .for_each(|symbol| {
                        gen.insert(symbol);
                    });
            }
            _ => ()
        }

        GenKillDecoratedThreeAddressCode {
            tac,
            gen,
            kill,
        }
    }
}

impl Display for GenKillDecoratedThreeAddressCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tac())?;
        write!(f, "     | GEN: ")?;
        self.gen().try_for_each(|x| write!(f, "{x} "))?;
        write!(f, "     | KILL: ")?;
        self.kill().try_for_each(|x| write!(f, "{x} "))
    }
}

/// Immutable basic block containing a sequence of
/// `GenKillDecoratedThreeAddressCode` nodes.
#[derive(Debug, PartialEq)]
pub struct GenKillDecoratedImmutableBasicBlock {
    label: BBLabel,
    seq: Vec<GenKillDecoratedThreeAddressCode>,

}

impl GenKillDecoratedImmutableBasicBlock {
    pub fn label(&self) -> BBLabel {
        self.label
    }

    pub fn seq(&self) -> &[GenKillDecoratedThreeAddressCode] {
        &self.seq
    }
}

impl From<ImmutableBasicBlock> for GenKillDecoratedImmutableBasicBlock {
    fn from(bb: ImmutableBasicBlock) -> Self {
        let (label, seq) = bb.into_parts();
        Self {
            label,
            seq: seq.into_iter()
                .map(|tac| Into::<GenKillDecoratedThreeAddressCode>::into(tac))
                .collect()
        }
    }
}

impl Display for GenKillDecoratedImmutableBasicBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:", self.label())?;
        for tac in self.seq() {
            writeln!(f, "{}", tac)?;
        }

        Ok(())
    }
}

/// Control flow graph containing `GenKillDecoratedImmutableBasicBlock`s.
#[derive(Debug, PartialEq)]
pub struct GenKillDecoratedControlFlowGraph {
    /// Basic block map - maps parent basic block
    /// to child basic blocks.
    bb_map: LinkedHashMap<BBLabel, Vec<BBLabel>>,
    /// List of basic blocks contained in the control
    /// flow graph.
    bbs: LinkedHashMap<BBLabel, GenKillDecoratedImmutableBasicBlock>,
}

impl GenKillDecoratedControlFlowGraph {
    pub fn basic_blocks(&self) -> impl Iterator<Item = (&BBLabel, &GenKillDecoratedImmutableBasicBlock)> {
        self.bbs.iter()
    }

    pub fn basic_block_map(&self) -> impl Iterator<Item = (&BBLabel, &Vec<BBLabel>)> {
        self.bb_map.iter()
    }
}

impl From<ControlFlowGraph> for GenKillDecoratedControlFlowGraph {
    fn from(cfg: ControlFlowGraph) -> Self {
        let (bb_map, bbs) = cfg.into_parts();
        Self {
            bb_map,
            bbs: bbs.into_iter()
                .map(|(bb_label, bb)| (bb_label, Into::<GenKillDecoratedImmutableBasicBlock>::into(bb)))
                .collect(),
        }
    }
}

impl Display for GenKillDecoratedControlFlowGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "==== Basic Blocks ===")?;
        for (_, bb) in self.basic_blocks() {
            writeln!(f, "{}", bb)?;
        }

        writeln!(f, "==== CFG ===")?;
        for (from, to) in self.basic_block_map() {
            writeln!(f, "{}: {:?}", from, to)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::cfg::basic_block::{ImmutableBasicBlock, BBLabel};
    use crate::three_addr_code_ir::{IdentI, TempI, BinaryExprOperandI, LValueI, FunctionIdent};
    use crate::symbol_table::symbol::{data, function};
    use std::rc::Rc;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
    use crate::cfg::liveness::{GenKillDecoratedImmutableBasicBlock, GenKillDecoratedThreeAddressCode, LValue};
    use std::collections::HashSet;
    use crate::symbol_table::{symbol_table_test_setup, SymbolTable};
    use crate::symbol_table::symbol::function::ReturnType;
    use serial_test::serial;

    #[test]
    fn push_instruction_gens_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![
            ThreeAddressCode::PushI (BinaryExprOperandI::LValue(LValueI::Id(a.clone()))),
        ];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `GenKillDecoratedImmutableBasicBlock`
        let expected_gen_kill_decorated_bb = GenKillDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::PushI (BinaryExprOperandI::LValue(LValueI::Id(a.clone()))),
                    gen: {
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        gen
                    },
                    kill: HashSet::new(),
                },
            ]
        };

        // Actual `GenKillDecoratedImmutableBasicBlock`
        let actual_gen_kill_decorated_bb: GenKillDecoratedImmutableBasicBlock = immutable_bb.into();
        assert_eq!(expected_gen_kill_decorated_bb, actual_gen_kill_decorated_bb);
    }

    #[test]
    fn pop_instruction_kills_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![
            ThreeAddressCode::PopI(LValueI::Id(a.clone())),
        ];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `GenKillDecoratedImmutableBasicBlock`
        let expected_gen_kill_decorated_bb = GenKillDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::PopI(LValueI::Id(a.clone())),
                    gen: HashSet::new(),
                    kill: {
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        kill
                    },
                },
            ]
        };

        // Actual `GenKillDecoratedImmutableBasicBlock`
        let actual_gen_kill_decorated_bb: GenKillDecoratedImmutableBasicBlock = immutable_bb.into();
        assert_eq!(expected_gen_kill_decorated_bb, actual_gen_kill_decorated_bb);
    }

    #[test]
    fn write_instruction_kills_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![
            ThreeAddressCode::WriteI {
                identifier: a.clone(),
            },
        ];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `GenKillDecoratedImmutableBasicBlock`
        let expected_gen_kill_decorated_bb = GenKillDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::WriteI {
                        identifier: a.clone(),
                    },
                    gen: {
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        gen
                    },
                    kill: HashSet::new(),
                },
            ]
        };

        // Actual `GenKillDecoratedImmutableBasicBlock`
        let actual_gen_kill_decorated_bb: GenKillDecoratedImmutableBasicBlock = immutable_bb.into();
        assert_eq!(expected_gen_kill_decorated_bb, actual_gen_kill_decorated_bb);
    }

    #[test]
    fn read_instruction_kills_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![
            ThreeAddressCode::ReadI {
                identifier: a.clone(),
            }
        ];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `GenKillDecoratedImmutableBasicBlock`
        let expected_gen_kill_decorated_bb = GenKillDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::ReadI {
                        identifier: a.clone(),
                    },
                    gen: HashSet::new(),
                    kill: {
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        kill
                    },
                },
            ]
        };

        // Actual `GenKillDecoratedImmutableBasicBlock`
        let actual_gen_kill_decorated_bb: GenKillDecoratedImmutableBasicBlock = immutable_bb.into();
        assert_eq!(expected_gen_kill_decorated_bb, actual_gen_kill_decorated_bb);
    }

    #[test]
    #[serial]
    fn call_instruction_gens_all_globals() {
        symbol_table_test_setup();

        let a = data::NonFunctionScopedSymbol::Int {
            name: "A".to_owned(),
        };
        let b = data::NonFunctionScopedSymbol::Int {
            name: "B".to_owned(),
        };
        let c = data::NonFunctionScopedSymbol::Int {
            name: "C".to_owned(),
        };

        SymbolTable::add_non_func_scoped_symbol(a.clone()).unwrap();
        SymbolTable::add_non_func_scoped_symbol(b.clone()).unwrap();
        SymbolTable::add_non_func_scoped_symbol(c.clone()).unwrap();

        let function_ident =
            FunctionIdent(Rc::new(function::Symbol::new("some_func".to_owned(), ReturnType::Void, vec![], vec![])));

        let seq = vec![
            ThreeAddressCode::Jsr(function_ident.clone()),
        ];

        let bb_label: BBLabel = 0.into();

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `GenKillDecoratedImmutableBasicBlock`
        let expected_gen_kill_decorated_bb = GenKillDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::Jsr(function_ident.clone()),
                    gen: {
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(IdentI(Rc::new(a.clone()).into()))));
                        gen.insert(LValue::LValueI(LValueI::Id(IdentI(Rc::new(b.clone()).into()))));
                        gen.insert(LValue::LValueI(LValueI::Id(IdentI(Rc::new(c.clone()).into()))));
                        gen
                    },
                    kill: HashSet::new(),
                },
            ]
        };

        // Actual `GenKillDecoratedImmutableBasicBlock`
        let actual_gen_kill_decorated_bb: GenKillDecoratedImmutableBasicBlock = immutable_bb.into();
        assert_eq!(expected_gen_kill_decorated_bb, actual_gen_kill_decorated_bb);
    }

    #[test]
    fn gen_kill_sets_for_bb() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));
        let b = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "B".to_owned(),
            },
        )));
        let c = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "C".to_owned(),
            },
        )));
        let d = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "D".to_owned(),
            },
        )));

        let (t1, t2): (TempI, TempI) = (1.into(), 2.into());
        let bb_label: BBLabel = 0.into();

        // d = a + b * c
        let seq = vec![
            ThreeAddressCode::MulI {
                lhs: BinaryExprOperandI::LValue(LValueI::Id(b.clone())),
                rhs: BinaryExprOperandI::LValue(LValueI::Id(c.clone())),
                temp_result: t1,
            },
            ThreeAddressCode::AddI {
                lhs: BinaryExprOperandI::LValue(LValueI::Temp(t1)),
                rhs: BinaryExprOperandI::LValue(LValueI::Id(a.clone())),
                temp_result: t2,
            },
            ThreeAddressCode::StoreI {
                lhs: LValueI::Id(d.clone()),
                rhs: BinaryExprOperandI::LValue(LValueI::Temp(t2))
            }
        ];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `GenKillDecoratedImmutableBasicBlock`
        let expected_gen_kill_decorated_bb = GenKillDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::MulI {
                        lhs: BinaryExprOperandI::LValue(LValueI::Id(b.clone())),
                        rhs: BinaryExprOperandI::LValue(LValueI::Id(c.clone())),
                        temp_result: t1,
                    },
                    gen: {
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(b.clone())));
                        gen.insert(LValue::LValueI(LValueI::Id(c.clone())));
                        gen
                    },
                    kill: {
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Temp(t1)));
                        kill
                    },
                },
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::AddI {
                        lhs: BinaryExprOperandI::LValue(LValueI::Temp(t1)),
                        rhs: BinaryExprOperandI::LValue(LValueI::Id(a.clone())),
                        temp_result: t2,
                    },
                    gen: {
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Temp(t1)));
                        gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        gen
                    },
                    kill: {
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Temp(t2)));
                        kill
                    },
                },
                GenKillDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::StoreI {
                        lhs: LValueI::Id(d.clone()),
                        rhs: BinaryExprOperandI::LValue(LValueI::Temp(t2))
                    },
                    gen: {
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Temp(t2)));
                        gen
                    },
                    kill: {
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Id(d.clone())));
                        kill
                    },
                },
            ]
        };

        // Actual `GenKillDecoratedImmutableBasicBlock`
        let actual_gen_kill_decorated_bb: GenKillDecoratedImmutableBasicBlock = immutable_bb.into();
        assert_eq!(expected_gen_kill_decorated_bb, actual_gen_kill_decorated_bb);
    }
}