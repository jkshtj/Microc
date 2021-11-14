//! Three Address Code Intermediate representation.
//! Type checking should happen at this stage.
use std::sync::atomic::{AtomicU64, Ordering};

use derive_more::Display;

use crate::symbol_table::{NumType, SymbolType};
use crate::ast::ast_node::Identifier;

pub mod three_address_code;


static TEMP_COUNTER: AtomicU64 = AtomicU64::new(1);
static LABEL_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Represents a point in the 3AC representation
/// required to support control flow.
#[derive(Debug, Display, Copy, Clone, Eq, PartialEq, Hash)]
#[display(fmt = "label{}", _0)]
pub struct Label(u64);

impl Label {
    pub fn new() -> Self {
        Self(LABEL_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

/// 3AC concept to represent int registers.
/// There is no limit to the number
/// of int temporaries that can be created.
#[derive(Debug, Copy, Clone, Display, Eq, PartialEq, Hash)]
#[display(fmt = "$T{}", _0)]
pub struct TempI(u64);

impl TempI {
    pub fn new() -> Self {
        Self(TEMP_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

/// 3AC concept to represent float registers.
/// There is no limit to the number
/// of int temporaries that can be created.
#[derive(Debug, Copy, Clone, Display, Eq, PartialEq, Hash)]
#[display(fmt = "$T{}", _0)]
pub struct TempF(u64);

impl TempF {
    pub fn new() -> Self {
        Self(TEMP_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

/// Int identifier
#[derive(Debug, Display, Clone)]
pub struct IdentI(pub String);

impl From<Identifier> for IdentI {
    fn from(id: Identifier) -> Self {
        IdentI(id.id)
    }
}

/// Float identifier
#[derive(Debug, Display, Clone)]
pub struct IdentF(pub String);

impl From<Identifier> for IdentF {
    fn from(id: Identifier) -> Self {
        IdentF(id.id)
    }
}

/// String identifier
#[derive(Debug, Display, Clone)]
pub struct IdentS(pub String);

impl From<Identifier> for IdentS {
    fn from(id: Identifier) -> Self {
        IdentS(id.id)
    }
}

/// Represents an int type LValue
/// that can either be a temporary
/// or an int identifier.
#[derive(Debug, Clone, Display)]
pub enum LValueI {
    Temp(TempI),
    #[display(fmt = "{}", _0)]
    Id(IdentI),
}

/// Represents an float type LValue
/// that can either be a temporary
/// or an float identifier.
#[derive(Debug, Clone, Display)]
pub enum LValueF {
    Temp(TempF),
    #[display(fmt = "{}", _0)]
    Id(IdentF),
}

/// Represents a RValue that can
/// either be an int or a float
/// literal.
#[derive(Debug, Clone, Display)]
pub enum RValue {
    IntLiteral(i32),
    FloatLiteral(f64),
}


#[derive(Debug, Clone, Display)]
pub enum BinaryExprOperand {
    LValueI(LValueI),
    LValueF(LValueF),
    RValue(RValue),
}

impl From<TempI> for BinaryExprOperand {
    fn from(temp: TempI) -> Self {
        BinaryExprOperand::LValueI(LValueI::Temp(temp))
    }
}

impl From<TempF> for BinaryExprOperand {
    fn from(temp: TempF) -> Self {
        BinaryExprOperand::LValueF(LValueF::Temp(temp))
    }
}

impl From<IdentI> for BinaryExprOperand {
    fn from(val: IdentI) -> Self {
        BinaryExprOperand::LValueI(LValueI::Id(val))
    }
}

impl From<IdentF> for BinaryExprOperand {
    fn from(val: IdentF) -> Self {
        BinaryExprOperand::LValueF(LValueF::Id(val))
    }
}

impl From<i32> for BinaryExprOperand {
    fn from(val: i32) -> Self {
        BinaryExprOperand::RValue(RValue::IntLiteral(val))
    }
}

impl From<f64> for BinaryExprOperand {
    fn from(val: f64) -> Self {
        BinaryExprOperand::RValue(RValue::FloatLiteral(val))
    }
}

impl From<LValueI> for BinaryExprOperand {
    fn from(lvalue: LValueI) -> Self {
        BinaryExprOperand::LValueI(lvalue)
    }
}

impl From<LValueF> for BinaryExprOperand {
    fn from(lvalue: LValueF) -> Self {
        BinaryExprOperand::LValueF(lvalue)
    }
}

impl From<RValue> for BinaryExprOperand {
    fn from(rvalue: RValue) -> Self {
        BinaryExprOperand::RValue(rvalue)
    }
}

// TODO: Move this to common types if there is a
//  use case outside of 3AC.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ResultType {
    String,
    Int,
    Float,
}

impl From<SymbolType> for ResultType {
    fn from(symbol_type: SymbolType) -> Self {
        match symbol_type {
            SymbolType::String => ResultType::String,
            SymbolType::Num(t) => {
                match t {
                    NumType::Int => ResultType::Int,
                    NumType::Float => ResultType::Float,
                }
            },
        }
    }
}