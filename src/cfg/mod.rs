use crate::cfg::basic_block::{BBFunction, BBLabel, ImmutableBasicBlock};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{LValueF, LValueI};
use linked_hash_map::LinkedHashMap;
use std::collections::HashSet;
use std::fmt::{Display, Formatter};

pub mod basic_block;
pub mod liveness;

#[derive(Debug, PartialEq)]
pub struct ControlFlowGraph {
    /// Basic block map - maps parent basic block
    /// to child basic blocks.
    bb_map: LinkedHashMap<BBLabel, Vec<BBLabel>>,
    /// List of basic blocks contained in the control
    /// flow graph.
    bbs: LinkedHashMap<BBLabel, ImmutableBasicBlock>,
}

impl Display for ControlFlowGraph {
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

impl ControlFlowGraph {
    #[cfg(test)]
    pub fn new(
        bb_map: LinkedHashMap<BBLabel, Vec<BBLabel>>,
        bbs: LinkedHashMap<BBLabel, ImmutableBasicBlock>,
    ) -> Self {
        Self { bb_map, bbs }
    }

    pub fn basic_blocks(&self) -> impl Iterator<Item = (&BBLabel, &ImmutableBasicBlock)> {
        self.bbs.iter()
    }

    pub fn basic_block_map(&self) -> impl Iterator<Item = (&BBLabel, &Vec<BBLabel>)> {
        self.bb_map.iter()
    }

    pub fn into_parts(
        self,
    ) -> (
        LinkedHashMap<BBLabel, Vec<BBLabel>>,
        LinkedHashMap<BBLabel, ImmutableBasicBlock>,
    ) {
        (self.bb_map, self.bbs)
    }
}

impl From<BBFunction> for ControlFlowGraph {
    fn from(bb_function: BBFunction) -> Self {
        fn create_edge(
            bb_map: &mut LinkedHashMap<BBLabel, Vec<BBLabel>>,
            from: BBLabel,
            to: BBLabel,
        ) {
            bb_map.entry(from).or_insert(vec![]).push(to);
        }

        let mut bb_map = LinkedHashMap::new();
        let (bbs, tac_label_to_bb_label_map) = bb_function.into_parts();
        // Tracking the prev bb and whether its
        // last statement is an unconditional jump
        // in order to create an edge between the prev
        // bb and the current bb - the current bb block
        // will be the fall through target of the prev bb.
        let mut prev_bb_label: Option<BBLabel> = None;
        let mut prev_bb_has_unconditional_jump = false;

        for (bb_label, bb) in bbs.iter() {
            let last_tac = bb.last();

            // If the current block is a fall through block of
            // the previous block, create an edge from the prev
            // block to the current block.
            if let Some(prev_bb_label) = prev_bb_label {
                if !prev_bb_has_unconditional_jump {
                    create_edge(&mut bb_map, prev_bb_label, *bb_label);
                }
            }
            prev_bb_label.replace(*bb_label);
            prev_bb_has_unconditional_jump = last_tac.is_unconditional_branch();

            // Create an edge to the explicit jump/branch target
            // of the current basic block.
            if let Some(tac_label) = last_tac.get_label_if_branch_or_jump() {
                create_edge(
                    &mut bb_map,
                    *bb_label,
                    tac_label_to_bb_label_map[&tac_label],
                );
            }
        }

        Self { bb_map, bbs }
    }
}

#[cfg(test)]
mod test {
    use crate::cfg::basic_block::{BBFunction, BBLabel};
    use crate::cfg::ControlFlowGraph;
    use crate::symbol_table::symbol::function::ReturnType;
    use crate::symbol_table::symbol::{data, function};
    use crate::three_addr_code_ir;
    use crate::three_addr_code_ir::three_address_code::visit::{
        CodeObject, ThreeAddressCodeVisitor,
    };
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode::{
        FunctionLabel, Jump, Label, Link, LteI, MulI, StoreI, WriteI,
    };
    use crate::three_addr_code_ir::{reset_label_counter, LValueI};
    use crate::three_addr_code_ir::{RValueI, FunctionIdent, IdentI, TempI};
    use linked_hash_map::LinkedHashMap;
    use serial_test::serial;
    use std::collections::HashMap;
    use std::rc::Rc;

    lalrpop_mod!(pub microc);

    #[test]
    #[serial]
    fn bb_function_to_cfg() {
        reset_label_counter();

        let program = r"
            PROGRAM sample
            BEGIN

                INT a, b, i, p;

                FUNCTION VOID main()
                BEGIN

                    a := 4;
                    b := 2;
                    p := a*b;

                    IF (p > 10)
                        i := 42;
                    ELSE
                        i := 24;
                    FI

                    WRITE (i);
                END
            END
        ";

        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "a".to_owned(),
            },
        )));
        let b = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "b".to_owned(),
            },
        )));
        let p = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "p".to_owned(),
            },
        )));
        let i = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "i".to_owned(),
            },
        )));

        let main = FunctionIdent(Rc::new(function::Symbol::new(
            "main".to_owned(),
            ReturnType::Void,
            vec![],
            vec![],
        )));
        let (t1, t2, t3, t4, t5, t6): (TempI, TempI, TempI, TempI, TempI, TempI) =
            (1.into(), 2.into(), 3.into(), 4.into(), 5.into(), 6.into());
        let (tac_label1, tac_label2): (three_addr_code_ir::Label, three_addr_code_ir::Label) =
            (1.into(), 2.into());
        let (bb_label0, bb_label1, bb_label2, bb_label3): (BBLabel, BBLabel, BBLabel, BBLabel) =
            (0.into(), 1.into(), 2.into(), 3.into());

        let mut bbs = LinkedHashMap::new();
        bbs.insert(
            bb_label0,
            (
                bb_label0,
                vec![
                    // LABEL main
                    FunctionLabel(main.clone()),
                    // LINK
                    Link(main),
                    // STOREI 4, $t1
                    StoreI {
                        lhs: LValueI::Temp(t1),
                        rhs: RValueI::RValue(4),
                    },
                    // STOREI $t1 a
                    StoreI {
                        lhs: LValueI::Id(a.clone()),
                        rhs: RValueI::LValue(LValueI::Temp(t1)),
                    },
                    // STOREI 2 $T2
                    StoreI {
                        lhs: LValueI::Temp(t2),
                        rhs: RValueI::RValue(2),
                    },
                    // STOREI $T2 b
                    StoreI {
                        lhs: LValueI::Id(b.clone()),
                        rhs: RValueI::LValue(LValueI::Temp(t2)),
                    },
                    // MULTI a b $T3
                    MulI {
                        lhs: LValueI::Id(a.clone()),
                        rhs: LValueI::Id(b.clone()),
                        temp_result: t3,
                    },
                    // STOREI $T3 p
                    StoreI {
                        lhs: LValueI::Id(p.clone()),
                        rhs: RValueI::LValue(LValueI::Temp(t3)),
                    },
                    // STOREI 10 $T4
                    StoreI {
                        lhs: LValueI::Temp(t4),
                        rhs: RValueI::RValue(10),
                    },
                    // LE p $T4 label1
                    LteI {
                        lhs: LValueI::Id(p.clone()),
                        rhs: LValueI::Temp(t4),
                        label: tac_label1,
                    },
                ],
            )
                .into(),
        );

        bbs.insert(
            bb_label1,
            (
                bb_label1,
                vec![
                    // STOREI 42 $T5
                    StoreI {
                        lhs: LValueI::Temp(t5),
                        rhs: RValueI::RValue(42),
                    },
                    // STOREI $T5 i
                    StoreI {
                        lhs: LValueI::Id(i.clone()),
                        rhs: RValueI::LValue(LValueI::Temp(t5)),
                    },
                    // JUMP label2
                    Jump(tac_label2),
                ],
            )
                .into(),
        );

        bbs.insert(
            bb_label2,
            (
                bb_label2,
                vec![
                    // LABEL label1
                    Label(tac_label1),
                    // STOREI 24 $T6
                    StoreI {
                        lhs: LValueI::Temp(t6),
                        rhs: RValueI::RValue(24),
                    },
                    // STOREI $T6 i
                    StoreI {
                        lhs: LValueI::Id(i.clone()),
                        rhs: RValueI::LValue(LValueI::Temp(t6)),
                    },
                    // JUMP label2
                    Jump(tac_label2),
                ],
            )
                .into(),
        );

        bbs.insert(
            bb_label3,
            (
                bb_label3,
                vec![
                    // LABEL label2
                    Label(tac_label2),
                    // WRITEI i
                    WriteI { identifier: i },
                ],
            )
                .into(),
        );

        let mut bb_map = LinkedHashMap::new();
        bb_map.insert(bb_label0, vec![bb_label2, bb_label1]);
        bb_map.insert(bb_label1, vec![bb_label3]);
        bb_map.insert(bb_label2, vec![bb_label3]);

        let expected_cfg = ControlFlowGraph::new(bb_map, bbs);

        // Parse program, generate 3AC, convert it into a `BBFunction` and convert `BBFunction` to a `ControlFlowGraph`
        let program = microc::ProgramParser::new().parse(&program);
        let mut result = program.unwrap();
        let mut visitor = ThreeAddressCodeVisitor;
        result.reverse();
        let cfg = result
            .into_iter()
            .map(|ast_node| visitor.walk_ast(ast_node))
            .map(|code_object| Into::<BBFunction>::into(code_object))
            .map(|bb_func| Into::<ControlFlowGraph>::into(bb_func))
            .last()
            .unwrap();

        /*
            Expected control flow graph -
            ```
            ==== Basic Blocks ===
            BB0:
            LABEL main
            LINK
            STOREI 4 $T1
            STOREI $T1 a
            STOREI 2 $T2
            STOREI $T2 b
            MULTI a b $T3
            STOREI $T3 p
            STOREI 10 $T4
            LE p $T4 label1

            BB1:
            STOREI 42 $T5
            STOREI $T5 i
            JUMP label2

            BB2:
            LABEL label1
            STOREI 24 $T6
            STOREI $T6 i
            JUMP label2

            BB3:
            LABEL label2
            WRITEI i

            ==== CFG ===
            BB0: [BBLabel(2), BBLabel(1)]
            BB1: [BBLabel(3)]
            BB2: [BBLabel(3)]
            ```
        */
        // println!("{expected_cfg}");
        // println!("{cfg}");

        assert_eq!(expected_cfg, cfg);
    }
}
