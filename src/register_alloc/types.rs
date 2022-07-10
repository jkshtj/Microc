use crate::cfg::liveness::LivenessMetadata;
use crate::symbol_table::symbol::data;
use crate::symbol_table::symbol::data::{FunctionScopedSymbol, FunctionScopedSymbolType};
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use crate::three_addr_code_ir::{IdentF, IdentI, LValue, LValueF, LValueI, TempF, TempI};
use std::collections::{HashMap, HashSet};
use std::ops::{Index, IndexMut};
use std::rc::Rc;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct RegisterId(usize);

impl RegisterId {
    pub fn into_inner(self) -> usize {
        self.0
    }
}

#[cfg(test)]
impl From<u32> for RegisterId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

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
#[derive(Debug, Clone)]
pub enum SpillType {
    Load,
    Store,
}

/// Represents a register spill.
#[derive(Debug, Clone)]
pub struct Spill {
    spill_type: SpillType,
    register_id: RegisterId,
    memory_location: data::Symbol,
}

impl Spill {
    #[cfg(test)]
    pub fn new(spill_type: SpillType, register_id: RegisterId, memory_location: data::Symbol) -> Self {
        Self {
            spill_type,
            register_id,
            memory_location
        }
    }

    pub fn into_parts(self) -> (SpillType, RegisterId, data::Symbol) {
        (self.spill_type, self.register_id, self.memory_location)
    }
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
            registers,
            stack_top_idx: 0,
            tempi_to_func_scoped_symbol_map: HashMap::new(),
            tempf_to_func_scoped_symbol_map: HashMap::new(),
        }
    }

    pub fn size(&self) -> usize {
        self.registers.len()
    }

    pub fn get_func_scoped_symbol_for_temp_int(&self, temp: TempI) -> Option<&FunctionScopedSymbol> {
        self.tempi_to_func_scoped_symbol_map.get(&temp)
    }

    pub fn add_func_scoped_symbol_for_temp_int(&mut self, temp: TempI, symbol: FunctionScopedSymbol) {
        let _ = self.tempi_to_func_scoped_symbol_map.insert(temp, symbol);
    }

    pub fn get_func_scoped_symbol_for_temp_float(&self, temp: TempF) -> Option<&FunctionScopedSymbol> {
        self.tempf_to_func_scoped_symbol_map.get(&temp)
    }

    pub fn add_func_scoped_symbol_for_temp_float(&mut self, temp: TempF, symbol: FunctionScopedSymbol) {
        let _ = self.tempf_to_func_scoped_symbol_map.insert(temp, symbol);
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
                let global_var = register.remove_value();
                match global_var {
                    Some(LValue::LValueI(LValueI::Id(IdentI(symbol)))) |
                    Some(LValue::LValueF(LValueF::Id(IdentF(symbol)))) => {
                        result.push(Spill {
                            spill_type: SpillType::Store,
                            register_id: register.id(),
                            memory_location: symbol,
                        });
                    }
                    _ => {}
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
        needs_load_spill: bool
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

        if needs_load_spill {
            // Since the operand is being used (GENed) (and
            // not defined (KILLed)), generate a `Load` type
            // spill as well.
            match operand {
                // If `operand` is a temporary it must have already
                // an associated function scoped symbol, at this point,
                // that we assigned to it when we allocated it a register.
                // We will generate a load type spill using this function
                // scoped symbol.
                LValue::LValueI(LValueI::Temp(temp)) => {
                    let symbol = self.get_func_scoped_symbol_for_temp_int(temp)
                        .expect("Expected an existing function scoped symbol for the int temporary but no associated function scoped symbol found.")
                        .clone();
                    allocation.add_spill(Spill {
                        spill_type: SpillType::Load,
                        register_id: allocation.register_id(),
                        memory_location: data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                    });
                }
                LValue::LValueF(LValueF::Temp(temp)) => {
                    let symbol = self.get_func_scoped_symbol_for_temp_float(temp)
                        .expect("Expected an existing function scoped symbol for the float temporary but no associated function scoped symbol found.")
                        .clone();
                    allocation.add_spill(Spill {
                        spill_type: SpillType::Load,
                        register_id: allocation.register_id(),
                        memory_location: data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                    });
                }
                LValue::LValueI(LValueI::Id(IdentI(symbol))) |
                LValue::LValueF(LValueF::Id(IdentF(symbol)))=> {
                    allocation.add_spill(Spill {
                        spill_type: SpillType::Load,
                        register_id: allocation.register_id(),
                        memory_location: symbol,
                    });
                }
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
        let allocation = if let Some(register_id) = self.get_free_register(liveness) {
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

        // If the operand to which we're allocating a register
        // is a temporary then we need to generate a function scoped
        // symbol for it. We will use this function scoped symbol
        // when we're generating spills for it while using it in
        // future instructions.
        match &operand {
            LValue::LValueI(LValueI::Temp(temp)) => {
                if self.get_func_scoped_symbol_for_temp_int(*temp).is_none() {
                    let symbol = FunctionScopedSymbol::Int {
                        symbol_type: FunctionScopedSymbolType::Local,
                        index: self.stack_top_idx,
                    };

                    self.stack_top_idx += 1;

                    self.add_func_scoped_symbol_for_temp_int(*temp, symbol.clone());
                }
            }
            LValue::LValueF(LValueF::Temp(temp)) => {
                if self.get_func_scoped_symbol_for_temp_float(*temp).is_none() {
                    let symbol = FunctionScopedSymbol::Float {
                        symbol_type: FunctionScopedSymbolType::Local,
                        index: self.stack_top_idx,
                    };

                    self.stack_top_idx += 1;

                    self.add_func_scoped_symbol_for_temp_float(*temp, symbol.clone());
                }
            }
            _ => {}
        }

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
        // is live, a `Store` type register spill must
        // be generated.
        if let Some(value) = curr_val {
            if liveness.is_var_live(&value) {
                match value {
                    LValue::LValueI(LValueI::Temp(temp)) => {
                        let symbol = self.get_func_scoped_symbol_for_temp_int(temp)
                            .expect("Expected an existing function scoped symbol for the int temporary but no associated function scoped symbol found.")
                            .clone();

                        return Some(Spill {
                            spill_type: SpillType::Store,
                            register_id,
                            memory_location: data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                        });
                    }
                    LValue::LValueF(LValueF::Temp(temp)) => {
                        let symbol = self.get_func_scoped_symbol_for_temp_float(temp)
                            .expect("Expected an existing function scoped symbol for the float temporary but no associated function scoped symbol found.")
                            .clone();

                        return Some(Spill {
                            spill_type: SpillType::Store,
                            register_id,
                            memory_location: data::Symbol::FunctionScopedSymbol(Rc::new(symbol)),
                        });
                    }
                    LValue::LValueI(LValueI::Id(IdentI(symbol))) |
                    LValue::LValueF(LValueF::Id(IdentF(symbol)))=> {
                        return Some(Spill {
                            spill_type: SpillType::Store,
                            register_id,
                            memory_location: symbol,
                        });
                    }
                }
            }
        }

        None
    }

    pub fn registers(&self) -> &Vec<Register> {
        &self.registers
    }

    fn registers_mut(&mut self) -> &mut Vec<Register> {
        &mut self.registers
    }

    fn get_free_register(&self, liveness: &LivenessMetadata) -> Option<RegisterId> {
        self.registers()
            .iter()
            // Look for free registers from the end
            .rev()
            // While looking for a free register, check -
            // 1. If there is a register with no associated value.
            //              OR
            // 2. If there is a register containing a value that
            //    is not USED (in GEN set) and LIVE (in OUT set).
            .filter(|&register| {
                if let Some(value) = register.value() {
                    !liveness.is_var_used(value) && !liveness.is_var_live(value)
                } else {
                    true
                }
            })
            .map(|register| register.id())
            .nth(0)
    }

    fn choose_register_to_free(&self, liveness: &LivenessMetadata) -> RegisterId {
        // TODO: What other heuristics can we use to determine
        //  which register to free? Distance of point of use
        //  from current instruction is one simple one however
        //  it is going to require knowledge of the liveness
        //  metadata of all instructions of the basic block.

        // If we are in this method, it means that there were
        // no registers with values that were both not USED and
        // not LIVE. That means that we're going to have to spill
        // a register containing a value that's not USED but may be
        // LIVE.
        let maybe_free_register = self
            .registers()
            .iter()
            .filter(|&register| {
                if let Some(value) = register.value() {
                    !liveness.is_var_used(value) && liveness.is_var_live(value)
                } else {
                    true
                }
            })
            .nth(0);

        if let Some(register) = maybe_free_register {
            return register.id();
        }

        // If no register with a non-live/dead value found
        // we need to panic as register allocation is not possible
        // in that case.
        panic!("Register Allocation NOT possible!");
    }
}

/// Represents 3AC with the operands that may
/// have been register allocated and may have
/// generated register spills.
#[derive(Debug, Clone)]
pub struct RegisterAllocatedThreeAddressCode {
    tac: ThreeAddressCode,
    register_allocations: HashMap<LValue, RegisterId>,
    spills: Vec<Spill>,
}

impl RegisterAllocatedThreeAddressCode {
    #[cfg(test)]
    pub fn new_for_test(tac: ThreeAddressCode, register_allocations: HashMap<LValue, RegisterId>, spills: Vec<Spill>) -> Self {
        Self {
            tac,
            register_allocations,
            spills
        }
    }

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

    pub fn into_parts(self) -> (ThreeAddressCode, HashMap<LValue, RegisterId>, Vec<Spill>) {
        (self.tac, self.register_allocations, self.spills)
    }
}
