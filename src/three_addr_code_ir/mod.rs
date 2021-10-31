//! Three Address Code Intermediate representation.
//! Type checking should happen at this stage.
use std::sync::atomic::{AtomicU64, Ordering};

use derive_more::Display;

use crate::symbol_table::{NumType, SymbolType};
use crate::ast::ast_node::Identifier;

pub mod three_address_code;


static TEMP_COUNTER: AtomicU64 = AtomicU64::new(1);

/// 3AC concept to represent registers.
/// There is no limit to the number
/// of temporaries that can be created.
#[derive(Debug, Copy, Clone, Display, Eq, PartialEq, Hash)]
#[display(fmt = "$T{}", id)]
pub struct Temporary {
    id: u64,
    num_type: NumType,
}

impl Temporary {
    pub fn new(num_type: NumType) -> Self {
        Self {
            id: TEMP_COUNTER.fetch_add(1, Ordering::SeqCst),
            num_type: num_type
        }
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
    Temp(Temporary),
    #[display(fmt = "{}", _0)]
    Id(IdentI),
}

/// Represents an float type LValue
/// that can either be a temporary
/// or an float identifier.
#[derive(Debug, Clone, Display)]
pub enum LValueF {
    Temp(Temporary),
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

impl From<Temporary> for BinaryExprOperand {
    fn from(temp: Temporary) -> Self {
        match temp.num_type {
            NumType::Int => BinaryExprOperand::LValueI(LValueI::Temp(temp)),
            NumType::Float => BinaryExprOperand::LValueF(LValueF::Temp(temp)),
        }
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
// use case outside of 3AC.
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