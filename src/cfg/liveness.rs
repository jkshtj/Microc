use crate::cfg::basic_block::{is_bb_terminator, BBLabel, ImmutableBasicBlock};
use crate::cfg::ControlFlowGraph;
use crate::symbol_table::symbol::data::DataType;
use crate::symbol_table::symbol::{data, NumType};
use crate::symbol_table::SymbolTable;
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{IdentF, IdentI, LValue, LValueF, LValueI, RValueF, RValueI};
use linked_hash_map::LinkedHashMap;
use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use typed_builder::TypedBuilder;

/// Represent the GEN, KILL, IN and OUT
/// sets associated to a 3AC node.
#[derive(Debug, PartialEq, TypedBuilder)]
#[builder(field_defaults(default, setter(transform = |x: HashSet<LValue>| Rc::new(RefCell::new(x)))))]
pub struct LivenessMetadata {
    gen_set: Rc<RefCell<HashSet<LValue>>>,
    kill_set: Rc<RefCell<HashSet<LValue>>>,
    in_set: Rc<RefCell<HashSet<LValue>>>,
    out_set: Rc<RefCell<HashSet<LValue>>>,
}

impl LivenessMetadata {
    #[cfg(test)]
    pub fn new(
        gen_set: HashSet<LValue>,
        kill_set: HashSet<LValue>,
        in_set: HashSet<LValue>,
        out_set: HashSet<LValue>,
    ) -> Self {
        Self {
            gen_set: Rc::new(RefCell::new(gen_set)),
            kill_set: Rc::new(RefCell::new(kill_set)),
            in_set: Rc::new(RefCell::new(in_set)),
            out_set: Rc::new(RefCell::new(out_set)),
        }
    }

    // TODO: Create a new to prevent leaking details
    // about the inner types, so that I could return something
    // like `impl TRAIT` instead of the concrete types I'm using
    // inside of `LivenessMetadata`.
    pub fn gen_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        Rc::clone(&self.gen_set)
    }

    pub fn kill_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        Rc::clone(&self.kill_set)
    }

    pub fn in_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        Rc::clone(&self.in_set)
    }

    pub fn out_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        Rc::clone(&self.out_set)
    }

    pub fn is_var_live(&self, var: &LValue) -> bool {
        self.out_set.borrow().contains(var)
    }

    pub fn is_var_used(&self, var: &LValue) -> bool {
        self.gen_set.borrow().contains(var)
    }
}

/// ThreeAddressCode nodes containing liveness
/// metadata for the current 3AC node.
#[derive(Debug, PartialEq)]
pub struct LivenessDecoratedThreeAddressCode {
    tac: ThreeAddressCode,
    liveness_metadata: LivenessMetadata,
}

impl LivenessDecoratedThreeAddressCode {
    #[cfg(test)]
    pub fn new(tac: ThreeAddressCode, liveness_metadata: LivenessMetadata) -> Self {
        Self {
            tac,
            liveness_metadata,
        }
    }

    pub fn gen_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        self.liveness_metadata.gen_set()
    }

    pub fn kill_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        self.liveness_metadata.kill_set()
    }

    pub fn in_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        self.liveness_metadata.in_set()
    }

    pub fn out_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        self.liveness_metadata.out_set()
    }

    pub fn tac(&self) -> &ThreeAddressCode {
        &self.tac
    }

    pub fn into_parts(self) -> (ThreeAddressCode, LivenessMetadata) {
        (self.tac, self.liveness_metadata)
    }
}

impl From<ThreeAddressCode> for LivenessDecoratedThreeAddressCode {
    fn from(tac: ThreeAddressCode) -> Self {
        let mut gen_set = HashSet::new();
        let mut kill_set = HashSet::new();
        let mut out_set = HashSet::new();

        match &tac {
            ThreeAddressCode::AddI {
                lhs,
                rhs,
                temp_result,
            }
            | ThreeAddressCode::SubI {
                lhs,
                rhs,
                temp_result,
            }
            | ThreeAddressCode::MulI {
                lhs,
                rhs,
                temp_result,
            }
            | ThreeAddressCode::DivI {
                lhs,
                rhs,
                temp_result,
            } => {
                gen_set.insert(LValue::LValueI(lhs.clone()));
                gen_set.insert(LValue::LValueI(rhs.clone()));

                kill_set.insert((*temp_result).into());
            }
            ThreeAddressCode::StoreI { lhs, rhs } => {
                if let RValueI::LValue(lvalue) = rhs {
                    gen_set.insert(LValue::LValueI(lvalue.clone()));
                }

                kill_set.insert(LValue::LValueI(lhs.clone()));
            }
            ThreeAddressCode::ReadI { identifier } => {
                kill_set.insert(LValue::LValueI(LValueI::Id(identifier.clone())));
            }
            ThreeAddressCode::WriteI { identifier } => {
                gen_set.insert(LValue::LValueI(LValueI::Id(identifier.clone())));
            }
            ThreeAddressCode::AddF {
                lhs,
                rhs,
                temp_result,
            }
            | ThreeAddressCode::SubF {
                lhs,
                rhs,
                temp_result,
            }
            | ThreeAddressCode::MulF {
                lhs,
                rhs,
                temp_result,
            }
            | ThreeAddressCode::DivF {
                lhs,
                rhs,
                temp_result,
            } => {
                gen_set.insert(LValue::LValueF(lhs.clone()));
                gen_set.insert(LValue::LValueF(rhs.clone()));

                kill_set.insert((*temp_result).into());
            }
            ThreeAddressCode::StoreF { lhs, rhs } => {
                if let RValueF::LValue(lvalue) = rhs {
                    gen_set.insert(LValue::LValueF(lvalue.clone()));
                }

                kill_set.insert(LValue::LValueF(lhs.clone()));
            }
            ThreeAddressCode::ReadF { identifier } => {
                kill_set.insert(LValue::LValueF(LValueF::Id(identifier.clone())));
            }
            ThreeAddressCode::WriteF { identifier } => {
                gen_set.insert(LValue::LValueF(LValueF::Id(identifier.clone())));
            }
            ThreeAddressCode::GtI { lhs, rhs, .. }
            | ThreeAddressCode::LtI { lhs, rhs, .. }
            | ThreeAddressCode::GteI { lhs, rhs, .. }
            | ThreeAddressCode::LteI { lhs, rhs, .. }
            | ThreeAddressCode::NeI { lhs, rhs, .. }
            | ThreeAddressCode::EqI { lhs, rhs, .. } => {
                gen_set.insert(LValue::LValueI(lhs.clone()));
                gen_set.insert(LValue::LValueI(rhs.clone()));
            }
            ThreeAddressCode::GtF { lhs, rhs, .. }
            | ThreeAddressCode::LtF { lhs, rhs, .. }
            | ThreeAddressCode::GteF { lhs, rhs, .. }
            | ThreeAddressCode::LteF { lhs, rhs, .. }
            | ThreeAddressCode::NeF { lhs, rhs, .. }
            | ThreeAddressCode::EqF { lhs, rhs, .. } => {
                gen_set.insert(LValue::LValueF(lhs.clone()));
                gen_set.insert(LValue::LValueF(rhs.clone()));
            }
            ThreeAddressCode::PushI(lvalue) => {
                gen_set.insert(LValue::LValueI(lvalue.clone()));
            }
            ThreeAddressCode::PushF(lvalue) => {
                gen_set.insert(LValue::LValueF(lvalue.clone()));
            }
            ThreeAddressCode::PopI(op) => {
                kill_set.insert(LValue::LValueI(op.clone()));
            }
            ThreeAddressCode::PopF(op) => {
                kill_set.insert(LValue::LValueF(op.clone()));
            }
            ThreeAddressCode::Jsr(_) => {
                SymbolTable::global_symbols()
                    .into_iter()
                    .filter_map(|symbol| match symbol.data_type() {
                        DataType::Num(NumType::Int) => {
                            Some(LValue::LValueI(LValueI::Id(IdentI(symbol.into()))))
                        }
                        DataType::Num(NumType::Float) => {
                            Some(LValue::LValueF(LValueF::Id(IdentF(symbol.into()))))
                        }
                        _ => None,
                    })
                    .for_each(|symbol| {
                        gen_set.insert(symbol);
                    });
            }
            // `Ret` 3AC is an exceptional instruction for which we don't add
            // any gen and use sets, but add the out set, which is always all
            // the globals present in the program because global variables may
            // be used after the function returns.
            ThreeAddressCode::Ret => {
                SymbolTable::global_symbols()
                    .into_iter()
                    .filter_map(|symbol| match symbol.data_type() {
                        DataType::Num(NumType::Int) => {
                            Some(LValue::LValueI(LValueI::Id(IdentI(symbol.into()))))
                        }
                        DataType::Num(NumType::Float) => {
                            Some(LValue::LValueF(LValueF::Id(IdentF(symbol.into()))))
                        }
                        _ => None,
                    })
                    .for_each(|symbol| {
                        out_set.insert(symbol);
                    });
            }
            _ => (),
        }

        LivenessDecoratedThreeAddressCode {
            tac,
            liveness_metadata: LivenessMetadata::builder()
                .gen_set(gen_set)
                .kill_set(kill_set)
                .out_set(out_set)
                .build(),
        }
    }
}

impl Display for LivenessDecoratedThreeAddressCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // With enough global variables, max_space might lead to an
        // overflow while calculating the different `space_*` values.
        let max_space = SymbolTable::global_symbols()
            .iter()
            .map(|x| x.name().len())
            .max()
            .map_or(30, |x| max(x * 10, 30));
        let space = max_space - self.tac().to_string().len();

        write!(f, "{}", self.tac())?;
        write!(f, "{:>space$}", "| LIVE: ")?;
        self.out_set()
            .borrow()
            .iter()
            .try_for_each(|x| write!(f, "{x}, "))?;

        write!(f, "| IN: ")?;
        self.in_set()
            .borrow()
            .iter()
            .try_for_each(|x| write!(f, "{x}, "))?;

        write!(f, "| GEN: ")?;
        self.gen_set()
            .borrow()
            .iter()
            .try_for_each(|x| write!(f, "{x}, "))?;

        write!(f, "| KILL: ")?;
        self.kill_set()
            .borrow()
            .iter()
            .try_for_each(|x| write!(f, "{x}, "))
    }
}

/// Immutable basic block containing a sequence of
/// `LivenessDecoratedThreeAddressCode` nodes.
#[derive(Debug, PartialEq)]
pub struct LivenessDecoratedImmutableBasicBlock {
    label: BBLabel,
    seq: Vec<LivenessDecoratedThreeAddressCode>,
}

impl LivenessDecoratedImmutableBasicBlock {
    pub fn label(&self) -> BBLabel {
        self.label
    }

    pub fn seq(&self) -> &[LivenessDecoratedThreeAddressCode] {
        &self.seq
    }

    fn first(&self) -> &LivenessDecoratedThreeAddressCode {
        // A basic block is guaranteed to never be empty
        &self.seq[0]
    }

    pub fn in_set(&self) -> Rc<RefCell<HashSet<LValue>>> {
        self.first().in_set()
    }

    pub fn into_parts(self) -> (BBLabel, Vec<LivenessDecoratedThreeAddressCode>) {
        (self.label, self.seq)
    }
}

impl From<ImmutableBasicBlock> for LivenessDecoratedImmutableBasicBlock {
    fn from(bb: ImmutableBasicBlock) -> Self {
        let (label, seq) = bb.into_parts();
        Self {
            label,
            seq: seq
                .into_iter()
                .map(Into::<LivenessDecoratedThreeAddressCode>::into)
                .collect(),
        }
    }
}

impl Display for LivenessDecoratedImmutableBasicBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:", self.label())?;
        for tac in self.seq() {
            writeln!(f, "{}", tac)?;
        }

        Ok(())
    }
}

#[cfg(test)]
impl From<(BBLabel, Vec<LivenessDecoratedThreeAddressCode>)>
    for LivenessDecoratedImmutableBasicBlock
{
    fn from(data: (BBLabel, Vec<LivenessDecoratedThreeAddressCode>)) -> Self {
        Self {
            label: data.0,
            seq: data.1,
        }
    }
}

/// Control flow graph containing `LivenessDecoratedImmutableBasicBlock`s.
#[derive(Debug, PartialEq)]
pub struct LivenessDecoratedControlFlowGraph {
    /// Basic block map - maps parent basic block
    /// to child basic blocks.
    bb_map: LinkedHashMap<BBLabel, Vec<BBLabel>>,
    /// List of basic blocks contained in the control
    /// flow graph.
    bbs: LinkedHashMap<BBLabel, LivenessDecoratedImmutableBasicBlock>,
}

impl LivenessDecoratedControlFlowGraph {
    #[cfg(test)]
    pub fn new(
        bb_map: LinkedHashMap<BBLabel, Vec<BBLabel>>,
        bbs: LinkedHashMap<BBLabel, LivenessDecoratedImmutableBasicBlock>,
    ) -> Self {
        Self { bb_map, bbs }
    }

    pub fn basic_blocks(
        &self,
    ) -> impl Iterator<Item = (&BBLabel, &LivenessDecoratedImmutableBasicBlock)> {
        self.bbs.iter()
    }

    pub fn into_basic_blocks(
        self,
    ) -> impl Iterator<Item = (BBLabel, LivenessDecoratedImmutableBasicBlock)> {
        self.bbs.into_iter()
    }

    pub fn basic_block_map(&self) -> impl Iterator<Item = (&BBLabel, &Vec<BBLabel>)> {
        self.bb_map.iter()
    }

    fn basic_block_for_label(
        &self,
        bb_label: &BBLabel,
    ) -> Option<&LivenessDecoratedImmutableBasicBlock> {
        self.bbs.get(bb_label)
    }

    fn neighbors_of_bb(&self, bb_label: &BBLabel) -> Option<&[BBLabel]> {
        self.bb_map
            .get(bb_label)
            .map(|neighbors| neighbors.as_slice())
    }

    /// Updates the in and out sets associated to each 3AC node
    /// present in the CFG's basic blocks.
    fn finalize_in_and_out_sets(&mut self) {
        /*
        1. Put all of the IR nodes on the worklist
        2. Pull an IR node off the worklist, and compute its OUT and IN sets.
        3. If the IN or OUT sets of the node get updated by the previous step, put all nodes back on the worklist.
        4. Repeat steps 2 and 3 until the worklist is empty.
        */
        loop {
            let worklist: Vec<(BBLabel, &LivenessDecoratedThreeAddressCode)> = {
                let mut worklist = self
                    .basic_blocks()
                    .flat_map(|(bb_label, bb)| bb.seq().iter().map(move |tac| (*bb_label, tac)))
                    .collect::<Vec<(BBLabel, &LivenessDecoratedThreeAddressCode)>>();

                // We cannot reverse the iterator before collecting worklist
                // items into a Vec because an iterator needs to implement
                // `DoubleEndedIterator` in order for it to be reversed. An
                // iterator created from a `LinkedHashMap` does not implement
                // the `DoubleEndedIterator` trait.
                worklist.reverse();

                worklist
            };

            let mut updated = false;
            let mut successor_tac_node_in_set: HashSet<LValue> = HashSet::new();

            for (bb_label, tac) in worklist {
                // Find current nodes successors. Two things -
                // 1. Since we are iterating the 3AC instructions for the
                // function in the reverse direction, the current node's successor's
                // IN set is stored in the `successor_tac_node_in_set` variable
                // declared above.
                //
                // 2. If this is a bb terminator then the current 3AC node may
                // have multiple successors.
                let mut out_set = HashSet::new();

                // If the current 3AC is not an unconditional jump then the
                // successor 3AC node's (which we actually visited in the previous
                // loop pass) IN set is part of the current 3AC node's OUT
                // set.
                if !tac.tac().is_unconditional_branch() {
                    out_set.extend(successor_tac_node_in_set);
                }

                // If this is a bb terminator then this 3AC node is
                // going to have multiple successors, that are the leaders
                // of other bbs in the function. We will use the IN sets
                // of those leaders to find/update this node's OUT set.
                if is_bb_terminator(tac.tac()) {
                    if let Some(neighbors_of_bb) = self.neighbors_of_bb(&bb_label) {
                        for neighboring_bb in neighbors_of_bb {
                            if let Some(neighbor) = self.basic_block_for_label(neighboring_bb) {
                                out_set.extend(neighbor.in_set().borrow().clone())
                            }
                        }
                    }
                }

                // Calculate the IN set for the current node.
                // IN = (OUT - KILL) U GEN
                let out_set_minus_kill_set = &out_set - &*tac.kill_set().borrow();
                let in_set = &out_set_minus_kill_set | &*tac.gen_set().borrow();

                let out_set_changed = out_set != *tac.out_set().borrow();
                let in_set_changed = in_set != *tac.in_set().borrow();

                if out_set_changed {
                    tac.out_set().borrow_mut().extend(out_set);
                }

                if in_set_changed {
                    tac.in_set().borrow_mut().extend(in_set.clone());
                }

                // `updated` is true if it has _once_ been set to true, or
                // if the current node's OUT or IN sets have changed.
                updated = updated || out_set_changed || in_set_changed;

                // Update successor_tac_node_in_set = in_set
                successor_tac_node_in_set = in_set;
            }

            if !updated {
                break;
            }
        }
    }
}

impl From<ControlFlowGraph> for LivenessDecoratedControlFlowGraph {
    fn from(cfg: ControlFlowGraph) -> Self {
        let (bb_map, bbs) = cfg.into_parts();
        let mut cfg = Self {
            bb_map,
            bbs: bbs
                .into_iter()
                .map(|(bb_label, bb)| {
                    (
                        bb_label,
                        Into::<LivenessDecoratedImmutableBasicBlock>::into(bb),
                    )
                })
                .collect(),
        };

        cfg.finalize_in_and_out_sets();
        cfg
    }
}

impl Display for LivenessDecoratedControlFlowGraph {
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
    use crate::cfg::basic_block::{BBFunction, BBLabel, ImmutableBasicBlock};
    use crate::cfg::liveness::{
        LValue, LivenessDecoratedControlFlowGraph, LivenessDecoratedImmutableBasicBlock,
        LivenessDecoratedThreeAddressCode, LivenessMetadata,
    };
    use crate::cfg::ControlFlowGraph;
    use crate::symbol_table::symbol::function::ReturnType;
    use crate::symbol_table::symbol::{data, function};
    use crate::symbol_table::{symbol_table_test_setup, SymbolTable};
    use crate::three_addr_code_ir;
    use crate::three_addr_code_ir::three_address_code::visit::ThreeAddressCodeVisitor;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode::{
        FunctionLabel, Jump, Label, Link, LteI, MulI, StoreI, WriteI,
    };
    use crate::three_addr_code_ir::{
        reset_label_counter, FunctionIdent, IdentI, LValueI, RValueI, TempI,
    };
    use linked_hash_map::LinkedHashMap;
    use serial_test::serial;
    use std::collections::HashSet;
    use std::rc::Rc;

    lalrpop_mod!(pub microc);

    #[test]
    fn push_instruction_gens_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![ThreeAddressCode::PushI(LValueI::Id(a.clone()))];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `LivenessDecoratedImmutableBasicBlock`
        let expected_liveness_decorated_bb = LivenessDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![LivenessDecoratedThreeAddressCode {
                tac: ThreeAddressCode::PushI(LValueI::Id(a.clone())),
                liveness_metadata: LivenessMetadata::builder()
                    .gen_set({
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        gen
                    })
                    .build(),
            }],
        };

        // Actual `LivenessDecoratedImmutableBasicBlock`
        let actual_liveness_decorated_bb: LivenessDecoratedImmutableBasicBlock =
            immutable_bb.into();
        assert_eq!(expected_liveness_decorated_bb, actual_liveness_decorated_bb);
    }

    #[test]
    fn pop_instruction_kills_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![ThreeAddressCode::PopI(LValueI::Id(a.clone()))];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `LivenessDecoratedImmutableBasicBlock`
        let expected_liveness_decorated_bb = LivenessDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![LivenessDecoratedThreeAddressCode {
                tac: ThreeAddressCode::PopI(LValueI::Id(a.clone())),
                liveness_metadata: LivenessMetadata::builder()
                    .kill_set({
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        kill
                    })
                    .build(),
            }],
        };

        // Actual `LivenessDecoratedImmutableBasicBlock`
        let actual_liveness_decorated_bb: LivenessDecoratedImmutableBasicBlock =
            immutable_bb.into();
        assert_eq!(expected_liveness_decorated_bb, actual_liveness_decorated_bb);
    }

    #[test]
    fn write_instruction_kills_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![ThreeAddressCode::WriteI {
            identifier: a.clone(),
        }];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `LivenessDecoratedImmutableBasicBlock`
        let expected_liveness_decorated_bb = LivenessDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![LivenessDecoratedThreeAddressCode {
                tac: ThreeAddressCode::WriteI {
                    identifier: a.clone(),
                },
                liveness_metadata: LivenessMetadata::builder()
                    .gen_set({
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        gen
                    })
                    .build(),
            }],
        };

        // Actual `LivenessDecoratedImmutableBasicBlock`
        let actual_liveness_decorated_bb: LivenessDecoratedImmutableBasicBlock =
            immutable_bb.into();
        assert_eq!(expected_liveness_decorated_bb, actual_liveness_decorated_bb);
    }

    #[test]
    fn read_instruction_kills_var_being_pushed() {
        let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
            data::NonFunctionScopedSymbol::Int {
                name: "A".to_owned(),
            },
        )));

        let bb_label: BBLabel = 0.into();

        let seq = vec![ThreeAddressCode::ReadI {
            identifier: a.clone(),
        }];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `LivenessDecoratedImmutableBasicBlock`
        let expected_liveness_decorated_bb = LivenessDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![LivenessDecoratedThreeAddressCode {
                tac: ThreeAddressCode::ReadI {
                    identifier: a.clone(),
                },
                liveness_metadata: LivenessMetadata::builder()
                    .kill_set({
                        let mut kill = HashSet::new();
                        kill.insert(LValue::LValueI(LValueI::Id(a.clone())));
                        kill
                    })
                    .build(),
            }],
        };

        // Actual `LivenessDecoratedImmutableBasicBlock`
        let actual_liveness_decorated_bb: LivenessDecoratedImmutableBasicBlock =
            immutable_bb.into();
        assert_eq!(expected_liveness_decorated_bb, actual_liveness_decorated_bb);
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

        let function_ident = FunctionIdent(Rc::new(function::Symbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![],
            vec![],
        )));

        let seq = vec![ThreeAddressCode::Jsr(function_ident.clone())];

        let bb_label: BBLabel = 0.into();

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `LivenessDecoratedImmutableBasicBlock`
        let expected_liveness_decorated_bb = LivenessDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![LivenessDecoratedThreeAddressCode {
                tac: ThreeAddressCode::Jsr(function_ident.clone()),
                liveness_metadata: LivenessMetadata::builder()
                    .gen_set({
                        let mut gen = HashSet::new();
                        gen.insert(LValue::LValueI(LValueI::Id(IdentI(
                            Rc::new(a.clone()).into(),
                        ))));
                        gen.insert(LValue::LValueI(LValueI::Id(IdentI(
                            Rc::new(b.clone()).into(),
                        ))));
                        gen.insert(LValue::LValueI(LValueI::Id(IdentI(
                            Rc::new(c.clone()).into(),
                        ))));
                        gen
                    })
                    .build(),
            }],
        };

        // Actual `LivenessDecoratedImmutableBasicBlock`
        let actual_liveness_decorated_bb: LivenessDecoratedImmutableBasicBlock =
            immutable_bb.into();
        assert_eq!(expected_liveness_decorated_bb, actual_liveness_decorated_bb);
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
                lhs: LValueI::Id(b.clone()),
                rhs: LValueI::Id(c.clone()),
                temp_result: t1,
            },
            ThreeAddressCode::AddI {
                lhs: LValueI::Temp(t1),
                rhs: LValueI::Id(a.clone()),
                temp_result: t2,
            },
            ThreeAddressCode::StoreI {
                lhs: LValueI::Id(d.clone()),
                rhs: RValueI::LValue(LValueI::Temp(t2)),
            },
        ];

        let immutable_bb: ImmutableBasicBlock = (bb_label, seq).into();

        // Expected `LivenessDecoratedImmutableBasicBlock`
        let expected_liveness_decorated_bb = LivenessDecoratedImmutableBasicBlock {
            label: immutable_bb.label(),
            seq: vec![
                LivenessDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::MulI {
                        lhs: LValueI::Id(b.clone()),
                        rhs: LValueI::Id(c.clone()),
                        temp_result: t1,
                    },
                    liveness_metadata: LivenessMetadata::builder()
                        .gen_set({
                            let mut gen = HashSet::new();
                            gen.insert(LValue::LValueI(LValueI::Id(b.clone())));
                            gen.insert(LValue::LValueI(LValueI::Id(c.clone())));
                            gen
                        })
                        .kill_set({
                            let mut kill = HashSet::new();
                            kill.insert(LValue::LValueI(LValueI::Temp(t1)));
                            kill
                        })
                        .build(),
                },
                LivenessDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::AddI {
                        lhs: LValueI::Temp(t1),
                        rhs: LValueI::Id(a.clone()),
                        temp_result: t2,
                    },
                    liveness_metadata: LivenessMetadata::builder()
                        .gen_set({
                            let mut gen = HashSet::new();
                            gen.insert(LValue::LValueI(LValueI::Temp(t1)));
                            gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                            gen
                        })
                        .kill_set({
                            let mut kill = HashSet::new();
                            kill.insert(LValue::LValueI(LValueI::Temp(t2)));
                            kill
                        })
                        .build(),
                },
                LivenessDecoratedThreeAddressCode {
                    tac: ThreeAddressCode::StoreI {
                        lhs: LValueI::Id(d.clone()),
                        rhs: RValueI::LValue(LValueI::Temp(t2)),
                    },
                    liveness_metadata: LivenessMetadata::builder()
                        .gen_set({
                            let mut gen = HashSet::new();
                            gen.insert(LValue::LValueI(LValueI::Temp(t2)));
                            gen
                        })
                        .kill_set({
                            let mut kill = HashSet::new();
                            kill.insert(LValue::LValueI(LValueI::Id(d.clone())));
                            kill
                        })
                        .build(),
                },
            ],
        };

        // Actual `LivenessDecoratedImmutableBasicBlock`
        let actual_liveness_decorated_bb: LivenessDecoratedImmutableBasicBlock =
            immutable_bb.into();
        assert_eq!(expected_liveness_decorated_bb, actual_liveness_decorated_bb);
    }

    #[test]
    #[serial]
    fn bb_function_to_liveness_decorated_cfg() {
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
                    LivenessDecoratedThreeAddressCode {
                        tac: FunctionLabel(main.clone()),
                        liveness_metadata: LivenessMetadata::builder().build(),
                    },
                    // LINK
                    LivenessDecoratedThreeAddressCode {
                        tac: Link(main),
                        liveness_metadata: LivenessMetadata::builder().build(),
                    },
                    // STOREI 4, $t1
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Temp(t1),
                            rhs: RValueI::RValue(4),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Temp(t1)));
                                kill
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Temp(t1)));
                                out
                            })
                            .build(),
                    },
                    // STOREI $t1 a
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Id(a.clone()),
                            rhs: RValueI::LValue(LValueI::Temp(t1)),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Temp(t1)));
                                gen
                            })
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Temp(t1)));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                out
                            })
                            .build(),
                    },
                    // STOREI 2 $T2
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Temp(t2),
                            rhs: RValueI::RValue(2),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Temp(t2)));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                out.insert(LValue::LValueI(LValueI::Temp(t2)));
                                out
                            })
                            .build(),
                    },
                    // STOREI $T2 b
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Id(b.clone()),
                            rhs: RValueI::LValue(LValueI::Temp(t2)),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Temp(t2)));
                                gen
                            })
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Id(b.clone())));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Temp(t2)));
                                in_set.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(b.clone())));
                                out.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                out
                            })
                            .build(),
                    },
                    // MULTI a b $T3
                    LivenessDecoratedThreeAddressCode {
                        tac: MulI {
                            lhs: LValueI::Id(a.clone()),
                            rhs: LValueI::Id(b.clone()),
                            temp_result: t3,
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Id(b.clone())));
                                gen.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                gen
                            })
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Temp(t3)));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(a.clone())));
                                in_set.insert(LValue::LValueI(LValueI::Id(b.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Temp(t3)));
                                out
                            })
                            .build(),
                    },
                    // STOREI $T3 p
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Id(p.clone()),
                            rhs: RValueI::LValue(LValueI::Temp(t3)),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Temp(t3)));
                                gen
                            })
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Id(p.clone())));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Temp(t3)));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(p.clone())));
                                out
                            })
                            .build(),
                    },
                    // STOREI 10 $T4
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Temp(t4),
                            rhs: RValueI::RValue(10),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Temp(t4)));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(p.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Temp(t4)));
                                out.insert(LValue::LValueI(LValueI::Id(p.clone())));
                                out
                            })
                            .build(),
                    },
                    // LE p $T4 label1
                    LivenessDecoratedThreeAddressCode {
                        tac: LteI {
                            lhs: LValueI::Id(p.clone()),
                            rhs: LValueI::Temp(t4),
                            label: tac_label1,
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Id(p.clone())));
                                gen.insert(LValue::LValueI(LValueI::Temp(t4)));
                                gen
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(p.clone())));
                                in_set.insert(LValue::LValueI(LValueI::Temp(t4)));
                                in_set
                            })
                            .build(),
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
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Temp(t5),
                            rhs: RValueI::RValue(42),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Temp(t5)));
                                kill
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Temp(t5)));
                                out
                            })
                            .build(),
                    },
                    // STOREI $T5 i
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Id(i.clone()),
                            rhs: RValueI::LValue(LValueI::Temp(t5)),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Temp(t5)));
                                gen
                            })
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Temp(t5)));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                out
                            })
                            .build(),
                    },
                    // JUMP label2
                    LivenessDecoratedThreeAddressCode {
                        tac: Jump(tac_label2),
                        liveness_metadata: LivenessMetadata::builder()
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                out
                            })
                            .build(),
                    },
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
                    LivenessDecoratedThreeAddressCode {
                        tac: Label(tac_label1),
                        liveness_metadata: LivenessMetadata::builder().build(),
                    },
                    // STOREI 24 $T6
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Temp(t6),
                            rhs: RValueI::RValue(24),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Temp(t6)));
                                kill
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Temp(t6)));
                                out
                            })
                            .build(),
                    },
                    // STOREI $T6 i
                    LivenessDecoratedThreeAddressCode {
                        tac: StoreI {
                            lhs: LValueI::Id(i.clone()),
                            rhs: RValueI::LValue(LValueI::Temp(t6)),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Temp(t6)));
                                gen
                            })
                            .kill_set({
                                let mut kill = HashSet::new();
                                kill.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                kill
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Temp(t6)));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                out
                            })
                            .build(),
                    },
                    // JUMP label2
                    LivenessDecoratedThreeAddressCode {
                        tac: Jump(tac_label2),
                        liveness_metadata: LivenessMetadata::builder()
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                out
                            })
                            .build(),
                    },
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
                    LivenessDecoratedThreeAddressCode {
                        tac: Label(tac_label2),
                        liveness_metadata: LivenessMetadata::builder()
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                in_set
                            })
                            .out_set({
                                let mut out = HashSet::new();
                                out.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                out
                            })
                            .build(),
                    },
                    // WRITEI i
                    LivenessDecoratedThreeAddressCode {
                        tac: WriteI {
                            identifier: i.clone(),
                        },
                        liveness_metadata: LivenessMetadata::builder()
                            .gen_set({
                                let mut gen = HashSet::new();
                                gen.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                gen
                            })
                            .in_set({
                                let mut in_set = HashSet::new();
                                in_set.insert(LValue::LValueI(LValueI::Id(i.clone())));
                                in_set
                            })
                            .build(),
                    },
                ],
            )
                .into(),
        );

        let mut bb_map = LinkedHashMap::new();
        bb_map.insert(bb_label0, vec![bb_label2, bb_label1]);
        bb_map.insert(bb_label1, vec![bb_label3]);
        bb_map.insert(bb_label2, vec![bb_label3]);

        let expected_cfg = LivenessDecoratedControlFlowGraph::new(bb_map, bbs);

        // Parse program, generate 3AC, convert it into a `BBFunction`, convert `BBFunction`
        // to a `ControlFlowGraph` and convert the `ControlFlowGraph` to a
        // `LivenessDecoratedControlFlowGraph`.
        let program = microc::ProgramParser::new().parse(&program);
        let mut result = program.unwrap();
        let mut visitor = ThreeAddressCodeVisitor;
        result.reverse();
        let cfg = result
            .into_iter()
            .map(|ast_node| visitor.walk_ast(ast_node))
            .map(|code_object| Into::<BBFunction>::into(code_object))
            .map(|bb_func| Into::<ControlFlowGraph>::into(bb_func))
            .map(|cfg| Into::<LivenessDecoratedControlFlowGraph>::into(cfg))
            .last()
            .unwrap();

        /*
            Expected liveness decorated control flow graph -
            ```
            ==== Basic Blocks ===
            BB0:
            LABEL main              | GEN:            | KILL:           | IN:           | OUT:
            LINK                    | GEN:            | KILL:           | IN:           | OUT:
            STOREI 4 $T1            | GEN:            | KILL: $T1,      | IN:           | OUT: $T1,
            STOREI $T1 a            | GEN: $T1,       | KILL: a,        | IN: $T1,      | OUT: a,
            STOREI 2 $T2            | GEN:            | KILL: $T2,      | IN: a,        | OUT: a, $T2,
            STOREI $T2 b            | GEN: $T2,       | KILL: b,        | IN: $T2, a,   | OUT: b, a,
            MULTI a b $T3           | GEN: b, a,      | KILL: $T3,      | IN: a, b,     | OUT: $T3,
            STOREI $T3 p            | GEN: $T3,       | KILL: p,        | IN: $T3,      | OUT: p,
            STOREI 10 $T4           | GEN:            | KILL: $T4,      | IN: p,        | OUT: $T4, p,
            LE p $T4 label1         | GEN: p, $T4,    | KILL:           | IN: p, $T4,   | OUT:

            BB1:
            STOREI 42 $T5           | GEN:            | KILL: $T5,      | IN:           | OUT: $T5,
            STOREI $T5 i            | GEN: $T5,       | KILL: i,        | IN: $T5,      | OUT: i,
            JUMP label2             | GEN:            | KILL:           | IN: i,        | OUT: i,

            BB2:
            LABEL label1            | GEN:            | KILL:           | IN:           | OUT:
            STOREI 24 $T6           | GEN:            | KILL: $T6,      | IN:           | OUT: $T6,
            STOREI $T6 i            | GEN: $T6,       | KILL: i,        | IN: $T6,      | OUT: i,
            JUMP label2             | GEN:            | KILL:           | IN: i,        | OUT: i,

            BB3:
            LABEL label2            | GEN:            | KILL:           | IN: i,        | OUT: i,
            WRITEI i                | GEN: i,         | KILL:           | IN: i,        | OUT:

            ==== CFG ===
            BB0: [BBLabel(2), BBLabel(1)]
            BB1: [BBLabel(3)]
            BB2: [BBLabel(3)]
            ```
        */
        println!("{expected_cfg}");
        // println!("{cfg}");

        assert_eq!(expected_cfg, cfg);
    }

    // TODO: Add unit test for a program with a loop
}
