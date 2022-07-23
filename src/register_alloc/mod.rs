use crate::cfg::basic_block::BBLabel;
use crate::cfg::liveness::{
    LivenessDecoratedControlFlowGraph, LivenessDecoratedThreeAddressCode, LivenessMetadata,
};
use crate::register_alloc::types::{
    RegisterAllocatedThreeAddressCode, RegisterFile, RegisterId, Spill,
};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{RValueF, RValueI};
use std::collections::HashSet;

pub mod types;

fn get_end_of_bb_spills(
    register_file: &mut RegisterFile,
    liveness_metadata: &LivenessMetadata,
) -> Vec<Spill> {
    // For BOTTOM-UP register allocation, at the
    // end of each basic block, for each dirty register, we need to
    // generate code to store the register into the associated
    // variable.
    //
    // While this may seem redundant in code without loops,
    // it is very much needed in code containing loops.
    register_file.free_dirty_registers(&liveness_metadata)
}

pub fn perform_register_allocation(
    cfg: LivenessDecoratedControlFlowGraph,
    register_file_size: usize,
) -> (Vec<RegisterAllocatedThreeAddressCode>, usize) {
    let mut tac_seq = vec![];
    let mut register_file = RegisterFile::new(register_file_size);

    cfg.into_basic_blocks().for_each(|(_, bb)| {
        let (_, bb_tac_seq) = bb.into_parts();

        let bb_size = bb_tac_seq.len();
        bb_tac_seq
            .into_iter()
            .enumerate()
            .for_each(|(i, liveness_decorated_tac)| {
                let (tac, liveness_metadata) = liveness_decorated_tac.into_parts();

                let mut reg_alloc_tac = match &tac {
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

                        // Ensure operands have a register
                        let lhs_reg_alloc = register_file.ensure_register(
                            lhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );
                        let rhs_reg_alloc = register_file.ensure_register(
                            rhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );

                        // Ensure the result has a register
                        let result_reg_alloc =
                            register_file.allocate_register(result.clone(), &liveness_metadata);

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lhs_lvalue) {
                            let _ = register_file
                                .free_register(lhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        if !liveness_metadata.is_var_live(&rhs_lvalue) {
                            let _ = register_file
                                .free_register(rhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                        register_file.set_register_dirty(result_reg_alloc.register_id());

                        reg_alloc_tac
                            .add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                        reg_alloc_tac
                            .add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());
                        reg_alloc_tac
                            .add_register_allocation(result, result_reg_alloc.register_id());

                        reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                        reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                        reg_alloc_tac.add_spills(result_reg_alloc.to_spills());

                        reg_alloc_tac
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

                        // Ensure operands have a register
                        let lhs_reg_alloc = register_file.ensure_register(
                            lhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );
                        let rhs_reg_alloc = register_file.ensure_register(
                            rhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );

                        // Ensure the result has a register
                        let result_reg_alloc =
                            register_file.allocate_register(result.clone(), &liveness_metadata);

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lhs_lvalue) {
                            let _ = register_file
                                .free_register(lhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        if !liveness_metadata.is_var_live(&rhs_lvalue) {
                            let _ = register_file
                                .free_register(rhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                        register_file.set_register_dirty(result_reg_alloc.register_id());

                        reg_alloc_tac
                            .add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                        reg_alloc_tac
                            .add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());
                        reg_alloc_tac
                            .add_register_allocation(result, result_reg_alloc.register_id());

                        reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                        reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                        reg_alloc_tac.add_spills(result_reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::StoreI { lhs, rhs } => {
                        // If rhs is not a literal ensure that it has a register.
                        // This same register that is allocated to rhs may be used
                        // by lhs.
                        let mut rhs_lvalue = None;
                        let mut rhs_reg_alloc = None;

                        if let RValueI::LValue(rhs) = rhs {
                            let inner_rhs_lvalue = rhs.to_lvalue();
                            let inner_rhs_reg_alloc = register_file.ensure_register(
                                inner_rhs_lvalue.clone(),
                                &liveness_metadata,
                                true,
                            );

                            rhs_lvalue.replace(inner_rhs_lvalue);
                            rhs_reg_alloc.replace(inner_rhs_reg_alloc);
                        }

                        // Ensure lhs has a register
                        let lhs_lvalue = lhs.to_lvalue();
                        let lhs_reg_alloc = register_file.ensure_register(
                            lhs_lvalue.clone(),
                            &liveness_metadata,
                            false,
                        );

                        // Free lhs operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lhs_lvalue) {
                            let _ = register_file
                                .free_register(lhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        // Free rhs operand register if operands are no longer live
                        if let Some(rhs_lvalue) = &rhs_lvalue {
                            if let Some(rhs_reg_alloc) = &rhs_reg_alloc {
                                // Free rhs operand register if operands are no longer live
                                if !liveness_metadata.is_var_live(&rhs_lvalue) {
                                    let _ = register_file.free_register(
                                        rhs_reg_alloc.register_id(),
                                        &liveness_metadata,
                                    );
                                }
                            }
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                        register_file.set_register_dirty(lhs_reg_alloc.register_id());

                        reg_alloc_tac
                            .add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                        reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());

                        if let Some(rhs_reg_alloc) = rhs_reg_alloc {
                            if let Some(rhs_lvalue) = rhs_lvalue {
                                reg_alloc_tac.add_register_allocation(
                                    rhs_lvalue,
                                    rhs_reg_alloc.register_id(),
                                );
                                reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                            }
                        }

                        reg_alloc_tac
                    }
                    ThreeAddressCode::StoreF { lhs, rhs } => {
                        // Ensure lhs has a register
                        let lhs_lvalue = lhs.to_lvalue();
                        let lhs_reg_alloc = register_file.ensure_register(
                            lhs_lvalue.clone(),
                            &liveness_metadata,
                            false,
                        );

                        // If rhs is not a literal ensure that it has a register.
                        // This same register that is allocated to rhs may be used
                        // by lhs.
                        let mut rhs_lvalue = None;
                        let mut rhs_reg_alloc = None;

                        if let RValueF::LValue(rhs) = rhs {
                            let inner_rhs_lvalue = rhs.to_lvalue();
                            let inner_rhs_reg_alloc = register_file.ensure_register(
                                inner_rhs_lvalue.clone(),
                                &liveness_metadata,
                                true,
                            );

                            rhs_lvalue.replace(inner_rhs_lvalue);
                            rhs_reg_alloc.replace(inner_rhs_reg_alloc);
                        }

                        // Free lhs operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lhs_lvalue) {
                            let _ = register_file
                                .free_register(lhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        // Free rhs operand register if operands are no longer live
                        if let Some(rhs_lvalue) = &rhs_lvalue {
                            if let Some(rhs_reg_alloc) = &rhs_reg_alloc {
                                // Free rhs operand register if operands are no longer live
                                if !liveness_metadata.is_var_live(&rhs_lvalue) {
                                    let _ = register_file.free_register(
                                        rhs_reg_alloc.register_id(),
                                        &liveness_metadata,
                                    );
                                }
                            }
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                        register_file.set_register_dirty(lhs_reg_alloc.register_id());

                        reg_alloc_tac
                            .add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                        reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());

                        if let Some(rhs_reg_alloc) = rhs_reg_alloc {
                            if let Some(rhs_lvalue) = rhs_lvalue {
                                reg_alloc_tac.add_register_allocation(
                                    rhs_lvalue,
                                    rhs_reg_alloc.register_id(),
                                );
                                reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());
                            }
                        }

                        reg_alloc_tac
                    }
                    ThreeAddressCode::ReadI { identifier }
                    | ThreeAddressCode::WriteI { identifier } => {
                        // Ensure operands have a register
                        let ident_lvalue = identifier.to_lvalue();
                        let ident_reg_alloc = register_file.ensure_register(
                            ident_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&ident_lvalue) {
                            let _ = register_file
                                .free_register(ident_reg_alloc.register_id(), &liveness_metadata);
                        } else if tac.is_read() {
                            register_file.set_register_dirty(ident_reg_alloc.register_id());
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                        reg_alloc_tac
                            .add_register_allocation(ident_lvalue, ident_reg_alloc.register_id());
                        reg_alloc_tac.add_spills(ident_reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::ReadF { identifier }
                    | ThreeAddressCode::WriteF { identifier } => {
                        // Ensure operands have a register
                        let ident_lvalue = identifier.to_lvalue();
                        let ident_reg_alloc = register_file.ensure_register(
                            ident_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&ident_lvalue) {
                            let _ = register_file
                                .free_register(ident_reg_alloc.register_id(), &liveness_metadata);
                        } else if tac.is_read() {
                            register_file.set_register_dirty(ident_reg_alloc.register_id());
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                        reg_alloc_tac
                            .add_register_allocation(ident_lvalue, ident_reg_alloc.register_id());
                        reg_alloc_tac.add_spills(ident_reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::GtI { lhs, rhs, .. }
                    | ThreeAddressCode::LtI { lhs, rhs, .. }
                    | ThreeAddressCode::GteI { lhs, rhs, .. }
                    | ThreeAddressCode::LteI { lhs, rhs, .. }
                    | ThreeAddressCode::NeI { lhs, rhs, .. }
                    | ThreeAddressCode::EqI { lhs, rhs, .. } => {
                        // Ensure operands have a register
                        let lhs_lvalue = lhs.to_lvalue();
                        let rhs_lvalue = rhs.to_lvalue();

                        let lhs_reg_alloc = register_file.ensure_register(
                            lhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );
                        let rhs_reg_alloc = register_file.ensure_register(
                            rhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lhs_lvalue) {
                            let _ = register_file
                                .free_register(lhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        if !liveness_metadata.is_var_live(&rhs_lvalue) {
                            let _ = register_file
                                .free_register(rhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                        reg_alloc_tac
                            .add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                        reg_alloc_tac
                            .add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());

                        reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                        reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::GtF { lhs, rhs, .. }
                    | ThreeAddressCode::LtF { lhs, rhs, .. }
                    | ThreeAddressCode::GteF { lhs, rhs, .. }
                    | ThreeAddressCode::LteF { lhs, rhs, .. }
                    | ThreeAddressCode::NeF { lhs, rhs, .. }
                    | ThreeAddressCode::EqF { lhs, rhs, .. } => {
                        // Ensure operands have a register
                        let lhs_lvalue = lhs.to_lvalue();
                        let rhs_lvalue = rhs.to_lvalue();

                        let lhs_reg_alloc = register_file.ensure_register(
                            lhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );
                        let rhs_reg_alloc = register_file.ensure_register(
                            rhs_lvalue.clone(),
                            &liveness_metadata,
                            true,
                        );

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lhs_lvalue) {
                            let _ = register_file
                                .free_register(lhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        if !liveness_metadata.is_var_live(&rhs_lvalue) {
                            let _ = register_file
                                .free_register(rhs_reg_alloc.register_id(), &liveness_metadata);
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);

                        reg_alloc_tac
                            .add_register_allocation(lhs_lvalue, lhs_reg_alloc.register_id());
                        reg_alloc_tac
                            .add_register_allocation(rhs_lvalue, rhs_reg_alloc.register_id());

                        reg_alloc_tac.add_spills(lhs_reg_alloc.to_spills());
                        reg_alloc_tac.add_spills(rhs_reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::PushI(lvalue) | ThreeAddressCode::PopI(lvalue) => {
                        // Ensure operands have a register
                        let lvalue = lvalue.to_lvalue();
                        let reg_alloc =
                            register_file.ensure_register(lvalue.clone(), &liveness_metadata, true);

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lvalue) {
                            let _ = register_file
                                .free_register(reg_alloc.register_id(), &liveness_metadata);
                        } else if tac.is_non_empty_pop() {
                            register_file.set_register_dirty(reg_alloc.register_id());
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                        reg_alloc_tac.add_register_allocation(lvalue, reg_alloc.register_id());
                        reg_alloc_tac.add_spills(reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::PushF(lvalue) | ThreeAddressCode::PopF(lvalue) => {
                        // Ensure operands have a register
                        let lvalue = lvalue.to_lvalue();
                        let reg_alloc =
                            register_file.ensure_register(lvalue.clone(), &liveness_metadata, true);

                        // Free operand register if operands are no longer live
                        if !liveness_metadata.is_var_live(&lvalue) {
                            let _ = register_file
                                .free_register(reg_alloc.register_id(), &liveness_metadata);
                        } else if tac.is_non_empty_pop() {
                            register_file.set_register_dirty(reg_alloc.register_id());
                        }

                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                        reg_alloc_tac.add_register_allocation(lvalue, reg_alloc.register_id());
                        reg_alloc_tac.add_spills(reg_alloc.to_spills());

                        reg_alloc_tac
                    }
                    ThreeAddressCode::FunctionLabel(funtion_ident) => {
                        register_file.set_stack_top_idx(funtion_ident.num_locals() + 1);
                        RegisterAllocatedThreeAddressCode::new(tac)
                    }
                    ThreeAddressCode::Jsr(_) => {
                        // Spill all registers with global vars before function calls
                        let spills =
                            register_file.free_registers_with_global_vars(&liveness_metadata);
                        let mut reg_alloc_tac = RegisterAllocatedThreeAddressCode::new(tac);
                        reg_alloc_tac.add_spills(spills);
                        reg_alloc_tac
                    }
                    // ThreeAddressCode::Ret => {}
                    _ => RegisterAllocatedThreeAddressCode::new(tac),
                };

                // If this is the last statement in the
                // basic block, generate the end of bb
                // spills and reset the register file.
                if i == bb_size - 1 {
                    reg_alloc_tac.add_end_of_bb_spills(get_end_of_bb_spills(
                        &mut register_file,
                        &liveness_metadata,
                    ));
                    register_file.reset_for_next_bb();
                }

                tac_seq.push(reg_alloc_tac);
            });
    });

    (tac_seq, register_file.stack_top_idx())
}

#[cfg(test)]
mod test {
    use crate::cfg::liveness::{LivenessDecoratedThreeAddressCode, LivenessMetadata};
    use crate::register_alloc::types::RegisterAllocatedThreeAddressCode;
    use crate::symbol_table::symbol::data;
    use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
    use crate::three_addr_code_ir::LValueI;
    use crate::three_addr_code_ir::{IdentI, RValueI, TempI};
    use std::rc::Rc;

    // #[test]
    // fn basic_conversion_to_reg_alloc_tac() {
    //     let a = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
    //         data::NonFunctionScopedSymbol::Int {
    //             name: "a".to_owned(),
    //         },
    //     )));
    //     let b = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
    //         data::NonFunctionScopedSymbol::Int {
    //             name: "b".to_owned(),
    //         },
    //     )));
    //     let c = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
    //         data::NonFunctionScopedSymbol::Int {
    //             name: "c".to_owned(),
    //         },
    //     )));
    //     let d = IdentI(data::Symbol::NonFunctionScopedSymbol(Rc::new(
    //         data::NonFunctionScopedSymbol::Int {
    //             name: "d".to_owned(),
    //         },
    //     )));
    //
    //     let (t1, t2, t3, t4): (TempI, TempI, TempI, TempI) = (1.into(), 2.into(), 3.into(), 4.into());
    //
    //
    //     /*
    //         3AC code sequence used -
    //             STOREI 2 $T1
    //             STOREI $T1 b
    //             STOREI 10 $T2
    //             STOREI $T2 c
    //             SUBI b c $T3
    //             STOREI $T3 a
    //             ADDI b a $T4
    //             STOREI $T4 d
    //             WRITEI a
    //             WRITEI b
    //             WRITEI c
    //             WRITEI d
    //      */
    //     let liveness_decorated_tac_seq = vec![
    //         // STOREI 2 $T1          | GEN:           	| KILL: $T1,          | IN:		   		   | LIVE: $T1,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Temp(t1),
    //                 rhs: RValueI::RValue(2)
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{},
    //                 hashset!{
    //                     t1.into()
    //                 },
    //                 hashset!{},
    //                 hashset!{
    //                     t1.into()
    //                 }
    //             )
    //         ),
    //
    //         // STOREI $T1 b          | GEN: $T1,       | KILL: b,            | IN: $T1,		   | LIVE: b,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(b.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t1))
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     t1.into()
    //                 },
    //                 hashset!{
    //                     b.clone().into()
    //                 },
    //                 hashset!{
    //                     t1.into()
    //                 },
    //                 hashset! {
    //                     b.clone().into()
    //                 }
    //             )
    //         ),
    //
    //         // STOREI 10 $T2         | GEN:          	| KILL: $T2,          | IN: b,		   	   | LIVE: b, $T2,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Temp(t2),
    //                 rhs: RValueI::RValue(10)
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{},
    //                 hashset!{
    //                     t2.into()
    //                 },
    //                 hashset!{
    //                     b.clone().into()
    //                 },
    //                 hashset! {
    //                     b.clone().into(),
    //                     t2.into(),
    //                 }
    //             )
    //         ),
    //
    //         // STOREI $T2 c          | GEN: $T2,       | KILL: c,            | IN: b, $T2,		   | LIVE: b, c,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(c.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t2))
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     t2.into()
    //                 },
    //                 hashset!{
    //                     c.clone().into()
    //                 },
    //                 hashset!{
    //                     b.clone().into(),
    //                     t2.into(),
    //                 },
    //                 hashset! {
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // SUBI b c $T3          | GEN: c, b,      | KILL: $T3,          | IN: b, c,		   | LIVE: $T3, c, b,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::SubI {
    //                 lhs: LValueI::Id(b.clone()),
    //                 rhs: LValueI::Id(c.clone()),
    //                 temp_result: t3
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 },
    //                 hashset!{
    //                     t3.into()
    //                 },
    //                 hashset!{
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 },
    //                 hashset! {
    //                     t3.into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // STOREI $T3 a          | GEN: $T3,       | KILL: a,            | IN: $T3, b, c,	   | LIVE: a, c, b,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(a.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t3))
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     t3.into()
    //                 },
    //                 hashset!{
    //                     a.clone().into()
    //                 },
    //                 hashset!{
    //                     t3.into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 },
    //                 hashset! {
    //                     a.clone().into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // ADDI b a $T4          | GEN: b, a,      | KILL: $T4,          | IN: b, a, c,	   | LIVE: a, c, b, $T4,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::AddI {
    //                 lhs: LValueI::Id(b.clone()),
    //                 rhs: LValueI::Id(a.clone()),
    //                 temp_result: t4
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     b.clone().into(),
    //                     a.clone().into(),
    //                 },
    //                 hashset!{
    //                     t4.into()
    //                 },
    //                 hashset!{
    //                     a.clone().into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 },
    //                 hashset! {
    //                     t4.into(),
    //                     a.clone().into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // STOREI $T4 d          | GEN: $T4,       | KILL: d,      | IN: a, b, $T4, c,  | LIVE: a, b, d, c,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(d.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t4))
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     t4.into()
    //                 },
    //                 hashset!{
    //                     d.clone().into()
    //                 },
    //                 hashset!{
    //                     t4.into(),
    //                     a.clone().into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                 },
    //                 hashset! {
    //                     a.clone().into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                     d.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // WRITEI a              | GEN: a,         | KILL:               | IN: b, a, d, c,	   | LIVE: c, d, b,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(a.0.clone()),
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     a.clone().into()
    //                 },
    //                 hashset!{},
    //                 hashset!{
    //                     a.clone().into(),
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                     d.clone().into(),
    //                 },
    //                 hashset! {
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                     d.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // WRITEI b              | GEN: b,         | KILL:               | IN: c, d, b,	   | LIVE: c, d,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(b.0.clone()),
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     b.clone().into()
    //                 },
    //                 hashset!{},
    //                 hashset!{
    //                     b.clone().into(),
    //                     c.clone().into(),
    //                     d.clone().into(),
    //                 },
    //                 hashset! {
    //                     c.clone().into(),
    //                     d.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // WRITEI c              | GEN: c,         | KILL:               | IN: d, c,		   | LIVE: d,
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(c.0.clone()),
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     c.clone().into()
    //                 },
    //                 hashset!{},
    //                 hashset!{
    //                     c.clone().into(),
    //                     d.clone().into(),
    //                 },
    //                 hashset! {
    //                     d.clone().into(),
    //                 }
    //             )
    //         ),
    //
    //         // WRITEI d              | GEN: d,         | KILL:               | IN: d,		   	   | LIVE:
    //         LivenessDecoratedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(d.0.clone()),
    //             },
    //             LivenessMetadata::new(
    //                 hashset!{
    //                     d.clone().into()
    //                 },
    //                 hashset!{},
    //                 hashset!{
    //                     d.clone().into(),
    //                 },
    //                 hashset! {}
    //             )
    //         ),
    //     ];
    //
    //     let expected_register_allocated_tac_seq = vec![
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Temp(t1),
    //                 rhs: RValueI::RValue(2)
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(b.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t1))
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Temp(t2),
    //                 rhs: RValueI::RValue(10)
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(c.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t2))
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::SubI {
    //                 lhs: LValueI::Id(b.clone()),
    //                 rhs: LValueI::Id(c.clone()),
    //                 temp_result: t3
    //             }
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(a.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t3))
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::AddI {
    //                 lhs: LValueI::Id(b.clone()),
    //                 rhs: LValueI::Id(a.clone()),
    //                 temp_result: t4
    //             }
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::StoreI {
    //                 lhs: LValueI::Id(d.clone()),
    //                 rhs: RValueI::LValue(LValueI::Temp(t4))
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(a.0.clone()),
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(b.0.clone()),
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(c.0.clone()),
    //             },
    //         ),
    //         RegisterAllocatedThreeAddressCode::new(
    //             ThreeAddressCode::WriteI {
    //                 identifier: IdentI(d.0.clone()),
    //             },
    //         ),
    //     ];
    // }

    // TODO: Modify tests to ensure correct end of bb spills are generated
}
