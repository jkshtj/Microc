use crate::cfg::basic_block::{BBFunction, BBLabel, ImmutableBasicBlock};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use linked_hash_map::LinkedHashMap;
use std::fmt::{Display, Formatter};

pub mod basic_block;

#[derive(Debug)]
pub struct ControlFlowGraph {
    cfg: LinkedHashMap<BBLabel, Vec<BBLabel>>,
    bbs: LinkedHashMap<BBLabel, ImmutableBasicBlock>,
}

impl Display for ControlFlowGraph {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "==== Basic Blocks ===")?;
        for (_, bb) in self.basic_blocks() {
            writeln!(f, "{}", bb)?;
        }

        writeln!(f, "==== CFG ===")?;
        for (from, to) in self.cfg() {
            writeln!(f, "{}: {:?}", from, to)?;
        }

        Ok(())
    }
}

impl ControlFlowGraph {
    pub fn new(
        cfg: LinkedHashMap<BBLabel, Vec<BBLabel>>,
        bbs: LinkedHashMap<BBLabel, ImmutableBasicBlock>,
    ) -> Self {
        Self { cfg, bbs }
    }

    pub fn basic_blocks(&self) -> impl Iterator<Item = (&BBLabel, &ImmutableBasicBlock)> {
        self.bbs.iter()
    }

    pub fn cfg(&self) -> impl Iterator<Item = (&BBLabel, &Vec<BBLabel>)> {
        self.cfg.iter()
    }
}

impl From<BBFunction> for ControlFlowGraph {
    fn from(bb_function: BBFunction) -> Self {
        fn create_edge(cfg: &mut LinkedHashMap<BBLabel, Vec<BBLabel>>, from: BBLabel, to: BBLabel) {
            cfg.entry(from).or_insert(vec![]).push(to);
        }

        let mut cfg = LinkedHashMap::new();
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
                    create_edge(&mut cfg, prev_bb_label, *bb_label);
                }
            }
            prev_bb_label.replace(*bb_label);
            prev_bb_has_unconditional_jump = last_tac.is_unconditional_branch();

            // Create an edge to the explicit jump/branch target
            // of the current basic block.
            if let Some(tac_label) = last_tac.get_label_if_branch_or_jump() {
                create_edge(&mut cfg, *bb_label, tac_label_to_bb_label_map[&tac_label]);
            }
        }

        Self { cfg, bbs }
    }
}

#[cfg(test)]
mod test {
    // TODO [unit tests]: Add unit tests
}
