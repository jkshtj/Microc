//! Three Address Code Intermediate representation.
//! Type checking should happen at this stage.
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ast::ast_node::Identifier;
use crate::symbol_table::symbol::NumType;
use crate::symbol_table::symbol::{data, function};
use std::rc::Rc;

pub mod three_address_code;

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(1);
static LABEL_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Resets the count of temporaries used so far. The
/// method is called once at the beginning of code gen
/// for each new `Function`.
pub fn reset_temp_counter() {
    TEMP_COUNTER.store(1, Ordering::SeqCst);
}

/// Resets the count of labels used so far.
#[cfg(test)]
pub fn reset_label_counter() {
    LABEL_COUNTER.store(1, Ordering::SeqCst);
}

/// Represents a point in the 3AC representation
/// required to support control flow.
#[derive(Debug, derive_more::Display, Copy, Clone, Eq, PartialEq, Hash)]
#[display(fmt = "label{}", _0)]
pub struct Label(u64);

impl Label {
    pub fn new() -> Self {
        Self(LABEL_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
    pub fn label(&self) -> u64 {
        self.0
    }
}

#[cfg(test)]
impl From<u64> for Label {
    fn from(n: u64) -> Self {
        Self(n)
    }
}

/// 3AC concept to represent int registers.
/// There is no limit to the number
/// of int temporaries that can be created.
#[derive(Debug, Copy, Clone, derive_more::Display, Eq, PartialEq, Hash)]
#[display(fmt = "$T{}", _0)]
pub struct TempI(u64);

impl TempI {
    pub fn new() -> Self {
        Self(TEMP_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

#[cfg(test)]
impl From<u64> for TempI {
    fn from(n: u64) -> Self {
        Self(n)
    }
}

/// 3AC concept to represent float registers.
/// There is no limit to the number
/// of float temporaries that can be created.
#[derive(Debug, Copy, Clone, derive_more::Display, Eq, PartialEq, Hash)]
#[display(fmt = "$T{}", _0)]
pub struct TempF(u64);

impl TempF {
    pub fn new() -> Self {
        Self(TEMP_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

/// Int identifier
#[derive(Debug, derive_more::Display, Clone, Eq, PartialEq, Hash)]
pub struct IdentI(pub data::Symbol);

impl From<Identifier> for IdentI {
    fn from(id: Identifier) -> Self {
        IdentI(id.symbol)
    }
}

/// Float identifier
#[derive(Debug, derive_more::Display, Clone, Eq, PartialEq, Hash)]
pub struct IdentF(pub data::Symbol);

impl From<Identifier> for IdentF {
    fn from(id: Identifier) -> Self {
        IdentF(id.symbol)
    }
}

/// String identifier
#[derive(Debug, derive_more::Display, Clone, Eq, PartialEq, Hash)]
pub struct IdentS(pub data::Symbol);

impl From<Identifier> for IdentS {
    fn from(id: Identifier) -> Self {
        IdentS(id.symbol)
    }
}

/// Represents an int type LValue
/// that can either be a temporary
/// or an int identifier.
#[derive(Debug, Clone, derive_more::Display, Eq, PartialEq, Hash)]
pub enum LValueI {
    Temp(TempI),
    #[display(fmt = "{}", _0)]
    Id(IdentI),
}

/// Represents an float type LValue
/// that can either be a temporary
/// or an float identifier.
#[derive(Debug, Clone, derive_more::Display, Eq, PartialEq, Hash)]
pub enum LValueF {
    Temp(TempF),
    #[display(fmt = "{}", _0)]
    Id(IdentF),
}

/// Represents an LValue that
/// may be an int or a float.
#[derive(Debug, Clone, derive_more::Display, Eq, PartialEq, Hash)]
pub enum LValue {
    LValueI(LValueI),
    LValueF(LValueF),
}

impl LValue {
    pub fn result_type(&self) -> ResultType {
        match self {
            LValue::LValueI(_) => ResultType::Int,
            LValue::LValueF(_) => ResultType::Float,
        }
    }
}

impl From<TempI> for LValue {
    fn from(temp: TempI) -> Self {
        LValue::LValueI(LValueI::Temp(temp))
    }
}

impl From<TempF> for LValue {
    fn from(temp: TempF) -> Self {
        LValue::LValueF(LValueF::Temp(temp))
    }
}

impl From<IdentI> for LValue {
    fn from(val: IdentI) -> Self {
        LValue::LValueI(LValueI::Id(val))
    }
}

impl From<IdentF> for LValue {
    fn from(val: IdentF) -> Self {
        LValue::LValueF(LValueF::Id(val))
    }
}

/// Integer type binary expression operand
#[derive(Debug, Clone, derive_more::Display, PartialEq)]
pub enum RValueI {
    LValue(LValueI),
    RValue(i32),
}

impl RValueI {
    pub fn is_mem_ref(&self) -> bool {
        matches!(self, RValueI::LValue(LValueI::Id(_)))
    }
}

impl From<TempI> for RValueI {
    fn from(temp: TempI) -> Self {
        RValueI::LValue(LValueI::Temp(temp))
    }
}

impl From<IdentI> for RValueI {
    fn from(val: IdentI) -> Self {
        RValueI::LValue(LValueI::Id(val))
    }
}

impl From<i32> for RValueI {
    fn from(val: i32) -> Self {
        RValueI::RValue(val)
    }
}

impl From<LValueI> for RValueI {
    fn from(lvalue: LValueI) -> Self {
        RValueI::LValue(lvalue)
    }
}

/// Float type binary expression operand
#[derive(Debug, Clone, derive_more::Display, PartialEq)]
pub enum RValueF {
    LValue(LValueF),
    RValue(f64),
}

impl RValueF {
    pub fn is_mem_ref(&self) -> bool {
        matches!(self, RValueF::LValue(LValueF::Id(_)))
    }
}

impl From<TempF> for RValueF {
    fn from(temp: TempF) -> Self {
        RValueF::LValue(LValueF::Temp(temp))
    }
}

impl From<IdentF> for RValueF {
    fn from(val: IdentF) -> Self {
        RValueF::LValue(LValueF::Id(val))
    }
}

impl From<f64> for RValueF {
    fn from(val: f64) -> Self {
        RValueF::RValue(val)
    }
}

impl From<LValueF> for RValueF {
    fn from(lvalue: LValueF) -> Self {
        RValueF::LValue(lvalue)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ResultType {
    Int,
    Float,
}

impl From<data::DataType> for ResultType {
    fn from(symbol_type: data::DataType) -> Self {
        match symbol_type {
            data::DataType::String => {
                panic!("STRING type is not a valid result of any 3AC operations.")
            }
            data::DataType::Num(t) => match t {
                NumType::Int => ResultType::Int,
                NumType::Float => ResultType::Float,
            },
        }
    }
}

/// Function identifier
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionIdent(pub Rc<function::Symbol>);

impl FunctionIdent {
    pub fn name(&self) -> &str {
        self.0.name()
    }
}
