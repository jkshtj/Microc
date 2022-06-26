//! Module to represent "basic blocks" representation of 3AC being generated
//! in the compiler middle-end.
//!
//! A basic block is a sequence of consecutive statements in which flow of control
//! can only enter at the beginning and leave at the end. Basic blocks are a means to
//! an end - generating control flow graphs, of which BBs are the primitive units.
//! Control flow graph is a form of code representation that captures the flow of control
//! in the code and aids us in performing middle-end optimizations, such as, register
//! allocation.
use crate::three_addr_code_ir::three_address_code::visit::CodeObject;
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::Label as ThreeAddrCodeLabel;
use linked_hash_map::LinkedHashMap;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::sync::atomic::{AtomicU64, Ordering};

static BB_COUNTER: AtomicU64 = AtomicU64::new(0);

fn reset_bb_counter() {
    BB_COUNTER.store(0, Ordering::SeqCst);
}

#[derive(Debug, Clone, Copy, derive_more::Display, Eq, PartialEq, Hash)]
#[display(fmt = "BB{}", _0)]
pub struct BBLabel(u64);

impl BBLabel {
    pub fn new() -> Self {
        Self(BB_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

#[cfg(test)]
impl From<u64> for BBLabel {
    fn from(n: u64) -> Self {
        Self(n)
    }
}

/// Represents a basic block. See
/// module level documentation for mor
/// information on basic blocks.
#[derive(Debug, PartialEq)]
struct BasicBlock {
    label: BBLabel,
    seq: Vec<ThreeAddressCode>,
}

impl BasicBlock {
    pub fn new() -> Self {
        Self {
            label: BBLabel::new(),
            seq: vec![],
        }
    }

    pub fn label(&self) -> BBLabel {
        self.label
    }

    pub fn add_tac(&mut self, tac: ThreeAddressCode) {
        self.seq.push(tac);
    }

    pub fn is_empty(&self) -> bool {
        self.seq.is_empty()
    }
}

/// Determines whether a given 3AC is a basic block
/// terminator. All branch/jump and return 3ACs can
/// be basic block terminators.
pub fn is_bb_terminator(tac: &ThreeAddressCode) -> bool {
    matches!(
        tac,
        // Unconditional jump
        ThreeAddressCode::Jump(_)
        // Conditional jump
        | ThreeAddressCode::GtI { .. }
        | ThreeAddressCode::LtI { .. }
        | ThreeAddressCode::GteI { .. }
        | ThreeAddressCode::LteI { .. }
        | ThreeAddressCode::NeI { .. }
        | ThreeAddressCode::EqI { .. }
        | ThreeAddressCode::GtF { .. }
        | ThreeAddressCode::LtF { .. }
        | ThreeAddressCode::GteF { .. }
        | ThreeAddressCode::LteF { .. }
        | ThreeAddressCode::NeF { .. }
        | ThreeAddressCode::EqF { .. }
    )
}

/// Same struct as the internal `BasicBlock` struct
/// but immutable and guaranteed to have at least one
/// statement present as its code sequence.
#[derive(Debug, PartialEq)]
pub struct ImmutableBasicBlock {
    label: BBLabel,
    seq: Vec<ThreeAddressCode>,
}

impl Display for ImmutableBasicBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:", self.label())?;
        for tac in self.seq() {
            writeln!(f, "{}", tac)?;
        }

        Ok(())
    }
}

impl ImmutableBasicBlock {
    pub fn label(&self) -> BBLabel {
        self.label
    }

    pub fn seq(&self) -> &[ThreeAddressCode] {
        &self.seq
    }

    pub fn last(&self) -> &ThreeAddressCode {
        // Safe to unwrap as an ImmutableBasicBlock will
        // always contain at least one 3AC.
        self.seq().last().unwrap()
    }

    pub fn into_parts(self) -> (BBLabel, Vec<ThreeAddressCode>) {
        (self.label, self.seq)
    }
}

impl From<BasicBlock> for ImmutableBasicBlock {
    fn from(bb: BasicBlock) -> Self {
        assert!(!bb.seq.is_empty());

        Self {
            label: bb.label,
            seq: bb.seq,
        }
    }
}

#[cfg(test)]
impl From<(BBLabel, Vec<ThreeAddressCode>)> for ImmutableBasicBlock {
    fn from(data: (BBLabel, Vec<ThreeAddressCode>)) -> Self {
        Self {
            label: data.0,
            seq: data.1,
        }
    }
}

/// Represents a container for the "basic block"
/// representation of the 3AC for a single
/// function. Our 3AC representation is essentially
/// the definition of a number of functions, one of
/// which is always `main`. However, in our 3AC
/// representation we don't have the concept of
/// code containers - that's essentially what this
/// type represents.
#[derive(Debug, PartialEq)]
pub struct BBFunction {
    bbs: LinkedHashMap<BBLabel, ImmutableBasicBlock>,
    tac_label_to_bb_label: HashMap<ThreeAddrCodeLabel, BBLabel>,
}

impl Display for BBFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "==== Basic Blocks ===")?;
        for bb in self.basic_blocks() {
            writeln!(f, "{}", bb)?;
        }

        writeln!(f, "==== 3AC Labels to BB Labels Mappings ===")?;
        for (tac_label, bb_label) in self.tac_label_to_bb_label_mappings() {
            writeln!(f, "{}: {}", tac_label, bb_label)?;
        }

        Ok(())
    }
}

impl BBFunction {
    pub fn new() -> Self {
        Self {
            bbs: LinkedHashMap::new(),
            tac_label_to_bb_label: HashMap::new(),
        }
    }

    pub fn basic_blocks(&self) -> impl Iterator<Item = &ImmutableBasicBlock> {
        self.bbs.values()
    }

    pub fn tac_label_to_bb_label_mappings(
        &self,
    ) -> impl Iterator<Item = (&ThreeAddrCodeLabel, &BBLabel)> {
        self.tac_label_to_bb_label.iter()
    }

    pub fn add_block(&mut self, bb: ImmutableBasicBlock) {
        self.bbs.insert(bb.label(), bb);
    }

    pub fn add_tac_label_to_bb_label_mapping(
        &mut self,
        tac_label: ThreeAddrCodeLabel,
        bb_label: BBLabel,
    ) {
        self.tac_label_to_bb_label.insert(tac_label, bb_label);
    }

    pub fn into_parts(
        self,
    ) -> (
        LinkedHashMap<BBLabel, ImmutableBasicBlock>,
        HashMap<ThreeAddrCodeLabel, BBLabel>,
    ) {
        (self.bbs, self.tac_label_to_bb_label)
    }
}

impl From<CodeObject> for BBFunction {
    fn from(code_object: CodeObject) -> Self {
        reset_bb_counter();
        let mut func = BBFunction::new();
        let mut curr_bb = BasicBlock::new();
        for tac in code_object.code_sequence {
            if is_bb_terminator(&tac) {
                // If the this 3AC is a conditional or unconditional
                // jump code then the we need to add the jump 3AC to
                // the current bb, close the current bb and then
                // start a new bb.
                // Immediately following statements to the current
                // statement are bb leaders as they are implicit targets
                // of branch instructions.
                curr_bb.add_tac(tac);
                func.add_block(curr_bb.into());
                curr_bb = BasicBlock::new()
            } else if let ThreeAddressCode::Label(label) = tac {
                // If this 3AC is a `Label` then we must close
                // the current bb, start a new bb and add the
                // label 3AC to the new bb. Current statement
                // is a bb leader as it an explicit target of
                // a conditional or unconditional branch.
                if !curr_bb.is_empty() {
                    func.add_block(curr_bb.into());
                    curr_bb = BasicBlock::new();
                }
                curr_bb.add_tac(tac);

                // Add a 3AC label to bb label mapping
                func.add_tac_label_to_bb_label_mapping(label, curr_bb.label());
            } else {
                // Otherwise we simply add the 3AC to the
                // curr bb.
                curr_bb.add_tac(tac);
            }
        }

        if !curr_bb.is_empty() {
            func.add_block(curr_bb.into());
        }

        func
    }
}

#[cfg(test)]
mod test {
    use crate::cfg::basic_block::{BBFunction, BBLabel};
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
    use crate::three_addr_code_ir::{FunctionIdent, IdentI, RValueI, TempI};
    use linked_hash_map::LinkedHashMap;
    use serial_test::serial;
    use std::collections::HashMap;
    use std::rc::Rc;

    lalrpop_mod!(pub microc);

    #[test]
    #[serial]
    fn code_object_to_bb_function() {
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

        let mut tac_label_to_bb_label = HashMap::new();
        tac_label_to_bb_label.insert(tac_label1, bb_label2);
        tac_label_to_bb_label.insert(tac_label2, bb_label3);

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

        let expected_bb_function = BBFunction {
            bbs,
            tac_label_to_bb_label,
        };

        // Parse program, generate 3AC and convert it into a `BBFunction`
        let program = microc::ProgramParser::new().parse(&program);
        let mut result = program.unwrap();
        let mut visitor = ThreeAddressCodeVisitor;
        result.reverse();
        let bb_function = result
            .into_iter()
            .map(|ast_node| visitor.walk_ast(ast_node))
            .map(|code_object| Into::<BBFunction>::into(code_object))
            .last()
            .unwrap();

        /*
            Expected basic blocks -
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

                ==== 3AC Labels to BB Labels Mappings ===
                label2: BB3
                label1: BB2
            ```
        */
        // println!("{expected_bb_function}");
        // println!("{bb_function}");

        assert_eq!(expected_bb_function, bb_function);
    }
}
