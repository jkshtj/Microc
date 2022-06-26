use crate::cfg::basic_block::BBLabel;
use crate::cfg::liveness::{
    LivenessDecoratedControlFlowGraph, LivenessDecoratedThreeAddressCode, LivenessMetadata,
};
use crate::register_alloc::types::{RegisterAllocatedThreeAddressCode, RegisterFile};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{RValueF, RValueI};

mod types;

pub fn perform_register_allocation(
    mut cfg: LivenessDecoratedControlFlowGraph,
    register_file_size: usize,
) -> Vec<RegisterAllocatedThreeAddressCode> {
    let mut tac_seq = vec![];
    let mut register_file = RegisterFile::new(register_file_size);

    cfg.into_basic_blocks().for_each(|(_, bb)| {
        let (_, bb_tac_seq) = bb.into_parts();
        bb_tac_seq.into_iter().for_each(|liveness_decorated_tac| {
            let (tac, liveness_metadata) = liveness_decorated_tac.into_parts();
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
                    let lhs_lvalue = lhs.to_lvalue();
                    let rhs_lvalue = rhs.to_lvalue();
                    let result = temp_result.to_lvalue();

                    let lhs_reg_alloc =
                        register_file.ensure_register(lhs_lvalue.clone(), &liveness_metadata);
                    let rhs_reg_alloc =
                        register_file.ensure_register(rhs_lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&lhs_lvalue) {
                        register_file.free_register(lhs_reg_alloc.register_id());
                    }

                    if !liveness_metadata.is_var_live(&rhs_lvalue) {
                        register_file.free_register(rhs_reg_alloc.register_id());
                    }

                    let result_reg_alloc =
                        register_file.allocate_register(result.clone(), &liveness_metadata);

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                    reg_alloc_tac.add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                    reg_alloc_tac.add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());
                    reg_alloc_tac.add_register_allocation(result, result_reg_alloc.register_id());

                    reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                    reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                    reg_alloc_tac.add_spills(result_reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
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
                    let lhs_lvalue = lhs.to_lvalue();
                    let rhs_lvalue = rhs.to_lvalue();
                    let result = temp_result.to_lvalue();

                    let lhs_reg_alloc =
                        register_file.ensure_register(lhs_lvalue.clone(), &liveness_metadata);
                    let rhs_reg_alloc =
                        register_file.ensure_register(rhs_lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&lhs_lvalue) {
                        register_file.free_register(lhs_reg_alloc.register_id());
                    }

                    if !liveness_metadata.is_var_live(&rhs_lvalue) {
                        register_file.free_register(rhs_reg_alloc.register_id());
                    }

                    let result_reg_alloc =
                        register_file.allocate_register(result.clone(), &liveness_metadata);

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                    reg_alloc_tac.add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                    reg_alloc_tac.add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());
                    reg_alloc_tac.add_register_allocation(result, result_reg_alloc.register_id());

                    reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                    reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                    reg_alloc_tac.add_spills(result_reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::StoreI { lhs, rhs } => {
                    let lhs_lvalue = lhs.to_lvalue();
                    let mut rhs_lvalue = None;
                    let lhs_reg_alloc =
                        register_file.ensure_register(lhs_lvalue.clone(), &liveness_metadata);
                    let mut rhs_reg_alloc = None;

                    if !liveness_metadata.is_var_live(&lhs_lvalue) {
                        register_file.free_register(lhs_reg_alloc.register_id());
                    }

                    if let RValueI::LValue(rhs) = rhs {
                        let inner_rhs_lvalue = rhs.to_lvalue();
                        let inner_rhs_reg_alloc = register_file
                            .ensure_register(inner_rhs_lvalue.clone(), &liveness_metadata);

                        if !liveness_metadata.is_var_live(&inner_rhs_lvalue) {
                            register_file.free_register(inner_rhs_reg_alloc.register_id());
                        }

                        rhs_lvalue.replace(inner_rhs_lvalue);
                        rhs_reg_alloc.replace(inner_rhs_reg_alloc);
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac.add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                    reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());

                    if let Some(rhs_reg_alloc) = rhs_reg_alloc {
                        if let Some(rhs_lvalue) = rhs_lvalue {
                            reg_alloc_tac
                                .add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());
                            reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                        }
                    }

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::StoreF { lhs, rhs } => {
                    let lhs_lvalue = lhs.to_lvalue();
                    let mut rhs_lvalue = None;
                    let lhs_reg_alloc =
                        register_file.ensure_register(lhs_lvalue.clone(), &liveness_metadata);
                    let mut rhs_reg_alloc = None;

                    if !liveness_metadata.is_var_live(&lhs_lvalue) {
                        register_file.free_register(lhs_reg_alloc.register_id());
                    }

                    if let RValueF::LValue(rhs) = rhs {
                        let inner_rhs_lvalue = rhs.to_lvalue();
                        let inner_rhs_reg_alloc = register_file
                            .ensure_register(inner_rhs_lvalue.clone(), &liveness_metadata);

                        if !liveness_metadata.is_var_live(&inner_rhs_lvalue) {
                            register_file.free_register(inner_rhs_reg_alloc.register_id());
                        }

                        rhs_lvalue.replace(inner_rhs_lvalue);
                        rhs_reg_alloc.replace(inner_rhs_reg_alloc);
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac.add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                    reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());

                    if let Some(rhs_reg_alloc) = rhs_reg_alloc {
                        if let Some(rhs_lvalue) = rhs_lvalue {
                            reg_alloc_tac
                                .add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());
                            reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                        }
                    }

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::ReadI { identifier }
                | ThreeAddressCode::WriteI { identifier } => {
                    let ident_lvalue = identifier.to_lvalue();
                    let ident_reg_alloc =
                        register_file.ensure_register(ident_lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&ident_lvalue) {
                        register_file.free_register(ident_reg_alloc.register_id());
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac
                        .add_register_allocation(ident_lvalue, ident_reg_alloc.register_id());
                    reg_alloc_tac.add_spills(ident_reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::ReadF { identifier }
                | ThreeAddressCode::WriteF { identifier } => {
                    let ident_lvalue = identifier.to_lvalue();
                    let ident_reg_alloc =
                        register_file.ensure_register(ident_lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&ident_lvalue) {
                        register_file.free_register(ident_reg_alloc.register_id());
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac
                        .add_register_allocation(ident_lvalue, ident_reg_alloc.register_id());
                    reg_alloc_tac.add_spills(ident_reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::GtI { lhs, rhs, .. }
                | ThreeAddressCode::LtI { lhs, rhs, .. }
                | ThreeAddressCode::GteI { lhs, rhs, .. }
                | ThreeAddressCode::LteI { lhs, rhs, .. }
                | ThreeAddressCode::NeI { lhs, rhs, .. }
                | ThreeAddressCode::EqI { lhs, rhs, .. } => {
                    let lhs_lvalue = lhs.to_lvalue();
                    let rhs_lvalue = rhs.to_lvalue();

                    let lhs_reg_alloc =
                        register_file.ensure_register(lhs_lvalue.clone(), &liveness_metadata);
                    let rhs_reg_alloc =
                        register_file.ensure_register(rhs_lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&lhs_lvalue) {
                        register_file.free_register(lhs_reg_alloc.register_id());
                    }

                    if !liveness_metadata.is_var_live(&rhs_lvalue) {
                        register_file.free_register(rhs_reg_alloc.register_id());
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                    reg_alloc_tac.add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                    reg_alloc_tac.add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());

                    reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                    reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::GtF { lhs, rhs, .. }
                | ThreeAddressCode::LtF { lhs, rhs, .. }
                | ThreeAddressCode::GteF { lhs, rhs, .. }
                | ThreeAddressCode::LteF { lhs, rhs, .. }
                | ThreeAddressCode::NeF { lhs, rhs, .. }
                | ThreeAddressCode::EqF { lhs, rhs, .. } => {
                    let lhs_lvalue = lhs.to_lvalue();
                    let rhs_lvalue = rhs.to_lvalue();

                    let lhs_reg_alloc =
                        register_file.ensure_register(lhs_lvalue.clone(), &liveness_metadata);
                    let rhs_reg_alloc =
                        register_file.ensure_register(rhs_lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&lhs_lvalue) {
                        register_file.free_register(lhs_reg_alloc.register_id());
                    }

                    if !liveness_metadata.is_var_live(&rhs_lvalue) {
                        register_file.free_register(rhs_reg_alloc.register_id());
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                    reg_alloc_tac.add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                    reg_alloc_tac.add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());

                    reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                    reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::PushI(lvalue) | ThreeAddressCode::PopI(lvalue) => {
                    let lvalue = lvalue.to_lvalue();
                    let reg_alloc =
                        register_file.ensure_register(lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&lvalue) {
                        register_file.free_register(reg_alloc.register_id());
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac.add_register_allocation(lvalue, reg_alloc.register_id());
                    reg_alloc_tac.add_spills(reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::PushF(lvalue) | ThreeAddressCode::PopF(lvalue) => {
                    let lvalue = lvalue.to_lvalue();
                    let reg_alloc =
                        register_file.ensure_register(lvalue.clone(), &liveness_metadata);

                    if !liveness_metadata.is_var_live(&lvalue) {
                        register_file.free_register(reg_alloc.register_id());
                    }

                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac.add_register_allocation(lvalue, reg_alloc.register_id());
                    reg_alloc_tac.add_spills(reg_alloc.to_spills());

                    tac_seq.push(reg_alloc_tac);
                }
                ThreeAddressCode::FunctionLabel(funtion_ident) => {
                    register_file.set_stack_top_idx(funtion_ident.num_locals() + 1);
                    tac_seq.push(RegisterAllocatedThreeAddressCode::new(tac));
                }
                ThreeAddressCode::Jsr(_) => {
                    // Spill all registers with global vars before function calls
                    let spills = register_file.free_registers_with_global_vars();
                    let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                    reg_alloc_tac.add_spills(spills);
                    tac_seq.push(reg_alloc_tac);
                }
                _ => tac_seq.push(RegisterAllocatedThreeAddressCode::new(tac)),
            }
        });

        // TODO: Apparently, for bottom up register allocation, at the
        // end of each basic block, for each dirty register, we need to
        // generate code to store the register into the associated
        // variable. **However** I'm not sure that's truly needed. I'll add
        // this if I run into issues.
    });

    tac_seq
}
