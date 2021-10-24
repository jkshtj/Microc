#[derive(Debug, Clone)]
pub struct Identifier {
    pub id: String,
    pub sym_type: SymbolType,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub enum NumType {
    Int,
    Float
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum SymbolType {
    String,
    Num(NumType),
}