use crate::cfg::liveness::{LivenessDecoratedControlFlowGraph, LivenessDecoratedThreeAddressCode, LivenessMetadata};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::cfg::basic_block::BBLabel;

mod types;

pub fn perform_register_allocation(mut cfg: LivenessDecoratedControlFlowGraph) -> Vec<ThreeAddressCode> {
    let mut tac_seq = vec![];
    let mut num_locals = 0;

    cfg.into_basic_blocks().for_each(|(_, bb)| {
        let (_, bb_tac_seq) = bb.into_parts();
        bb_tac_seq.into_iter().for_each(|liveness_decorated_tac| {
            let (tac, liveness_metadata) = liveness_decorated_tac.into_parts();
            match tac {
                ThreeAddressCode::AddI {
                    lhs,
                    rhs,
                    temp_result
                } => {
                    // ensure lhs
                    // ensure rhs
                    // free lhs and rhs if they're not live after this instruction
                    // allocate reg for temp_result
                }
                ThreeAddressCode::SubI { .. } => {}
                ThreeAddressCode::MulI { .. } => {}
                ThreeAddressCode::DivI { .. } => {}
                ThreeAddressCode::StoreI { .. } => {}
                ThreeAddressCode::ReadI { .. } => {}
                ThreeAddressCode::WriteI { .. } => {}
                ThreeAddressCode::AddF { .. } => {}
                ThreeAddressCode::SubF { .. } => {}
                ThreeAddressCode::MulF { .. } => {}
                ThreeAddressCode::DivF { .. } => {}
                ThreeAddressCode::StoreF { .. } => {}
                ThreeAddressCode::ReadF { .. } => {}
                ThreeAddressCode::WriteF { .. } => {}
                ThreeAddressCode::WriteS { .. } => {}
                ThreeAddressCode::Label(_) => {}
                ThreeAddressCode::Jump(_) => {}
                ThreeAddressCode::GtI { .. } => {}
                ThreeAddressCode::LtI { .. } => {}
                ThreeAddressCode::GteI { .. } => {}
                ThreeAddressCode::LteI { .. } => {}
                ThreeAddressCode::NeI { .. } => {}
                ThreeAddressCode::EqI { .. } => {}
                ThreeAddressCode::GtF { .. } => {}
                ThreeAddressCode::LtF { .. } => {}
                ThreeAddressCode::GteF { .. } => {}
                ThreeAddressCode::LteF { .. } => {}
                ThreeAddressCode::NeF { .. } => {}
                ThreeAddressCode::EqF { .. } => {}
                ThreeAddressCode::FunctionLabel(_) => {}
                ThreeAddressCode::Jsr(_) => {}
                ThreeAddressCode::Link(_) => {}
                ThreeAddressCode::Ret => {}
                ThreeAddressCode::PushEmpty => {}
                ThreeAddressCode::PushI(_) => {}
                ThreeAddressCode::PushF(_) => {}
                ThreeAddressCode::PopEmpty => {}
                ThreeAddressCode::PopI(_) => {}
                ThreeAddressCode::PopF(_) => {}
            }
        });

        // At the end of each basic block, for each dirty register
        // generate code to store the register into the associated
        // variable.
    });

    tac_seq
}