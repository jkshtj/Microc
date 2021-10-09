pub mod token;
pub mod decl;

#[allow(unused)]
pub enum VarType {
    String,
    Num(NumType),
    Void,
}

pub enum NumType {
    Int,
    Float
}
