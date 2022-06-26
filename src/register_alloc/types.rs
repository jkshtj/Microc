use crate::cfg::liveness::LivenessMetadata;
use crate::symbol_table::symbol::data;
use crate::symbol_table::symbol::data::{FunctionScopedSymbol, FunctionScopedSymbolType};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{IdentF, IdentI, LValue, LValueF, LValueI, TempF, TempI};
use std::collections::{HashMap, HashSet};
use std::ops::{Index, IndexMut};
use std::rc::Rc;
use tracing::callsite::register;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct RegisterId(usize);

impl Index<RegisterId> for RegisterFile {
    type Output = Register;

    fn index(&self, index: RegisterId) -> &Self::Output {
        &self.registers()[index.0]
    }
}

impl IndexMut<RegisterId> for RegisterFile {
    fn index_mut(&mut self, index: RegisterId) -> &mut Self::Output {
        &mut self.registers_mut()[index.0]
    }
}

/// Construct used to represent the concept of a
/// hardware independent register allocated during
/// register allocation.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Register {
    id: RegisterId,
    value: Option<LValue>,
}

impl Register {
    pub fn id(&self) -> RegisterId {
        self.id
    }

    pub fn value(&self) -> Option<&LValue> {
        self.value.as_ref()
    }

    pub fn is_dirty(&self) -> bool {
        self.value.is_some()
    }

    pub fn remove_value(&mut self) -> Option<LValue> {
        self.value.take()
    }

    pub fn set_value(&mut self, value: LValue) {
        let _ = self.value.replace(value);
    }
}

/// Type of spill during register allocation.
/// `Load` happens when there is a free register and value
/// has to be read from memory.
/// `Store` happens when there are no free registers and a
/// dirty register needs to be freed by writing its value to
/// the tracked memory location.
#[derive(Debug)]
pub enum SpillType {
    Load,
    Store,
}

/// Represents a register spill.
#[derive(Debug)]
pub struct Spill {
    spill_type: SpillType,
    register_id: RegisterId,
    memory_location: LValue,
}

/// Represents the result of a register allocation.
/// Consists of the register allocated and any spill
/// code that might have been generated as a result.
#[derive(Debug)]
pub struct RegisterAllocation {
    register_id: RegisterId,
    spills: Vec<Spill>,
}

impl RegisterAllocation {
    pub fn register_id(&self) -> RegisterId {
        self.register_id
    }

    pub fn spills(&self) -> &Vec<Spill> {
        &self.spills
    }

    pub fn to_spills(self) -> Vec<Spill> {
        self.spills
    }

    fn add_spill(&mut self, spill: Spill) {
        self.spills.push(spill);
    }
}

/// Construct representing the concept
/// of a set of hardware independent registers
/// and used for tracking the state of registers
/// during register allocation.
#[derive(Debug)]
pub struct RegisterFile {
    size: usize,
    registers: Vec<Register>,
    /// Current stack top value for the
    /// function we're register allocating
    /// the code for. It starts at 1 plus
    /// number of locals in the function.
    stack_top_idx: usize,
    /// Stores the function scoped symbol mapped
    /// to an int temporary if it were spilled.
    tempi_to_func_scoped_symbol_map: HashMap<TempI, FunctionScopedSymbol>,
    /// Stores the function scoped symbol mapped
    /// to a float temporary if it were spilled.
    tempf_to_func_scoped_symbol_map: HashMap<TempF, FunctionScopedSymbol>,
}

impl RegisterFile {
    pub fn new(size: usize) -> Self {
        let registers = (0..size)
            .map(|n| Register {
                id: RegisterId(n),
                value: None,
            })
            .collect();

        Self {
            size,
            registers,
            stack_top_idx: 0,
            tempi_to_func_scoped_symbol_map: HashMap::new(),
            tempf_to_func_scoped_symbol_map: HashMap::new(),
        }
    }

    pub fn set_stack_top_idx(&mut self, stack_top_idx: usize) {
        self.stack_top_idx = stack_top_idx;
    }

    pub fn free_registers_with_global_vars(&mut self) -> Vec<Spill> {
        let mut result = vec![];

        self.registers_mut().iter_mut().for_each(|register| {
            let is_reg_val_global_var = register
                .value()
                .map_or(false, |value| value.is_global_var());

            if is_reg_val_global_var {
                if let Some(value) = register.remove_value() {
                    result.push(Spill {
                        spill_type: SpillType::Store,
                        register_id: register.id(),
                        memory_location: value,
                    });
                }
            }
        });

        result
    }

    pub fn free_dirty_registers(&mut self, liveness: &LivenessMetadata) -> Vec<Spill> {
        let mut result = vec![];

        let dirty_register_ids: Vec<RegisterId> = self
            .registers()
            .iter()
            .filter(|&register| register.is_dirty())
            .map(|register| register.id())
            .collect();

        dirty_register_ids.into_iter().for_each(|id| {
            if let Some(spill) = self.free_register_with_liveness_check(id, liveness) {
                result.push(spill);
            }
        });

        result
    }

    pub fn ensure_register(
        &mut self,
        operand: LValue,
        liveness: &LivenessMetadata,
    ) -> RegisterAllocation {
        // If operand is in a register return the register.
        let maybe_register_containing_value = self
            .registers()
            .iter()
            .filter(|&register| {
                if let Some(value) = register.value() {
                    value == &operand
                } else {
                    false
                }
            })
            .nth(0);

        if let Some(register) = maybe_register_containing_value {
            return RegisterAllocation {
                register_id: register.id(),
                spills: vec![],
            };
        }

        // Else, allocate a register for the operand.
        let mut allocation = self.allocate_register(operand.clone(), liveness);

        // Since the operand is being used (GENed) (and
        // not defined (KILLed)), generate a `Load` type
        // spill as well.
        match &operand {
            // If `operand` is a temporary it must have been spilled
            // to the stack earlier in the program and we should have
            // generated a function scoped symbol to keep track of it.
            // Let's get the associated function scoped symbol that we
            // assigned to it and generate a load type spill using it.
            LValue::LValueI(LValueI::Temp(temp)) => {
                let symbol = self.tempi_to_func_scoped_symbol_map.get(temp)
                    .expect("Expected an existing function scoped for the int temporary but associated function scoped symbol found.")
                    .clone();
                allocation.add_spill(Spill {
                    spill_type: SpillType::Load,
                    register_id: allocation.register_id(),
                    memory_location: LValue::LValueI(LValueI::Id(IdentI(
                        data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                    ))),
                });
            }
            LValue::LValueF(LValueF::Temp(temp)) => {
                let symbol = self.tempf_to_func_scoped_symbol_map.get(temp)
                    .expect("Expected an existing function scoped for the int temporary but associated function scoped symbol found.")
                    .clone();
                allocation.add_spill(Spill {
                    spill_type: SpillType::Load,
                    register_id: allocation.register_id(),
                    memory_location: LValue::LValueF(LValueF::Id(IdentF(
                        data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                    ))),
                });
            }
            _ => {
                allocation.add_spill(Spill {
                    spill_type: SpillType::Load,
                    register_id: allocation.register_id(),
                    memory_location: operand,
                });
            }
        }

        allocation
    }

    pub fn allocate_register(
        &mut self,
        operand: LValue,
        liveness: &LivenessMetadata,
    ) -> RegisterAllocation {
        // If there is a free register, allocate it.
        let allocation = if let Some(register_id) = self.get_free_register() {
            RegisterAllocation {
                register_id,
                spills: vec![],
            }
        } else {
            // Else, free a register and allocate it.
            let register_to_free = self.choose_register_to_free(liveness);
            let maybe_store_type_spill =
                self.free_register_with_liveness_check(register_to_free, liveness);
            RegisterAllocation {
                register_id: register_to_free,
                spills: maybe_store_type_spill.map_or(vec![], |spill| vec![spill]),
            }
        };

        // Finally, associate operand to the newly allocated register.
        // to the operand.
        let register = &mut self[allocation.register_id()];
        register.set_value(operand);

        allocation
    }

    pub fn free_register(&mut self, register_id: RegisterId) {
        let register = &mut self[register_id];
        let _ = register.remove_value();
    }

    fn free_register_with_liveness_check(
        &mut self,
        register_id: RegisterId,
        liveness: &LivenessMetadata,
    ) -> Option<Spill> {
        let register = &mut self[register_id];

        let curr_val = register.remove_value();

        // If register is dirty and its current value
        // is live a `Store` type register spill must
        // be generated.
        if let Some(value) = curr_val {
            if liveness.is_var_live(&value) {
                match value {
                    // If the current value stored in the register is a temporary
                    // which is live, then we should spill it to the stack as a new
                    // function scoped symbol. The temporary may already have been
                    // spilled to the stack at some earlier point in the program in
                    // which case we will not need to generate a new function scoped
                    // symbol.
                    LValue::LValueI(LValueI::Temp(temp)) => {
                        let symbol =
                            if let Some(symbol) = self.tempi_to_func_scoped_symbol_map.get(&temp) {
                                symbol.clone()
                            } else {
                                let symbol = FunctionScopedSymbol::Int {
                                    symbol_type: FunctionScopedSymbolType::Local,
                                    index: self.stack_top_idx,
                                };

                                self.stack_top_idx += 1;

                                symbol
                            };

                        return Some(Spill {
                            spill_type: SpillType::Store,
                            register_id,
                            memory_location: LValue::LValueI(LValueI::Id(IdentI(
                                data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                            ))),
                        });
                    }
                    LValue::LValueF(LValueF::Temp(temp)) => {
                        let symbol =
                            if let Some(symbol) = self.tempf_to_func_scoped_symbol_map.get(&temp) {
                                symbol.clone()
                            } else {
                                let symbol = FunctionScopedSymbol::Float {
                                    symbol_type: FunctionScopedSymbolType::Local,
                                    index: self.stack_top_idx,
                                };

                                self.stack_top_idx += 1;

                                symbol
                            };

                        return Some(Spill {
                            spill_type: SpillType::Store,
                            register_id,
                            memory_location: LValue::LValueF(LValueF::Id(IdentF(
                                data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                            ))),
                        });
                    }
                    _ => {
                        return Some(Spill {
                            spill_type: SpillType::Store,
                            register_id,
                            memory_location: value,
                        });
                    }
                }
            }
        }

        None
    }

    fn registers(&self) -> &Vec<Register> {
        &self.registers
    }

    fn registers_mut(&mut self) -> &mut Vec<Register> {
        &mut self.registers
    }

    fn get_free_register(&self) -> Option<RegisterId> {
        self.registers()
            .iter()
            .filter(|&register| !register.is_dirty())
            .map(|register| register.id())
            .nth(0)
    }

    fn choose_register_to_free(&self, liveness: &LivenessMetadata) -> RegisterId {
        // TODO: What other heuristics can we use to determine
        //  which register to free? Distance of point of use
        //  from current instruction is one simple one however
        //  it is going to require knowledge of the liveness
        //  metadata of all instructions of the basic block.

        // Try and find a register whose value is not live.
        let maybe_free_register = self
            .registers()
            .iter()
            .filter(|&register| {
                if let Some(value) = register.value() {
                    !liveness.is_var_live(value)
                } else {
                    false
                }
            })
            .nth(0);

        if let Some(register) = maybe_free_register {
            return register.id();
        }

        // If no register with a non-live/dead value found
        // return the first register in the register file.
        RegisterId(0)
    }
}

/// Represents 3AC with the operands that may
/// have been register allocated and may have
/// generated register spills.
#[derive(Debug)]
pub struct RegisterAllocatedThreeAddressCode {
    tac: ThreeAddressCode,
    register_allocations: HashMap<LValue, RegisterId>,
    spills: Vec<Spill>,
}

impl RegisterAllocatedThreeAddressCode {
    pub fn new(tac: ThreeAddressCode) -> Self {
        Self {
            tac,
            register_allocations: HashMap::new(),
            spills: Vec::new(),
        }
    }

    pub fn add_spills(&mut self, spills: Vec<Spill>) {
        self.spills.extend(spills);
    }

    pub fn add_register_allocation(&mut self, lvalue: LValue, register_id: RegisterId) {
        self.register_allocations.insert(lvalue, register_id);
    }
}
