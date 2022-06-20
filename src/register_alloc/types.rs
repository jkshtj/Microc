use crate::symbol_table::symbol::data;
use crate::three_addr_code_ir::{LValue, LValueI, IdentI, LValueF, IdentF};
use std::collections::{HashSet, HashMap};
use crate::cfg::liveness::LivenessMetadata;
use crate::three_addr_code_ir::three_address_code::ThreeAddressCode;
use std::ops::{Index, IndexMut};
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
        }
    }

    pub fn ensure_register(&mut self, operand: LValue, liveness: &LivenessMetadata) -> RegisterAllocation {
        // If operand is in a register return the register.
        let maybe_register_containing_value = self.registers()
            .iter()
            .filter(|&register| if let Some(value) = register.value() {
                value == &operand
            } else {
                false
            })
            .nth(0);

        if let Some(register) = maybe_register_containing_value {
            return RegisterAllocation {
                register_id: register.id(),
                spills: vec![]
            };
        }

        // Else, allocate a register for the operand.
        let mut allocation = self.allocate_register(operand.clone(), liveness);

        // Since the operand is being used (GENed) (and
        // not defined (KILLed)), generate a `Load` type
        // spill as well.
        allocation.add_spill(Spill {
            spill_type: SpillType::Load,
            register_id: allocation.register_id(),
            memory_location: operand,
        });

        allocation
    }

    pub fn allocate_register(&mut self, operand: LValue, liveness: &LivenessMetadata) -> RegisterAllocation {
        // If there is a free register, allocate it.
        let allocation = if let Some(register_id) = self.get_free_register() {
            RegisterAllocation {
                register_id,
                spills: vec![],
            }
        } else { // Else, free a register and allocate it.
            let register_to_free = self.choose_register_to_free(liveness);
            let maybe_store_type_spill = self.free_register(register_to_free, liveness);
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

    fn free_register(&mut self, register_id: RegisterId, liveness: &LivenessMetadata) -> Option<Spill> {
        let register = &mut self[register_id];

        let curr_val = register.remove_value();

        // If register is dirty and its current value
        // is live a `Store` type register spill must
        // be generated.
        if let Some(value) = curr_val {
            if liveness.is_var_live(&value) {
                return Some(Spill {
                    spill_type: SpillType::Store,
                    register_id,
                    memory_location: value,
                })

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
        let maybe_free_register = self.registers()
            .iter()
            .filter(|&register| if let Some(value) = register.value() {
                !liveness.is_var_live(value)
            } else {
                false
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
    register_allocations: HashMap<LValue, Register>,
    spills: Vec<SpillType>,
}