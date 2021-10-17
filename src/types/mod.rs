use crate::symbol_table::SymbolType;

#[derive(Debug, Clone)]
pub struct Identifier {
    pub id: String,
    pub sym_type: SymbolType,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum NumType {
    Int,
    Float
}
