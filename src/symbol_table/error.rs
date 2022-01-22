use getset::Getters;

/// Type to represent errors originating
/// from multiple symbol declarations with
/// the same name in the same scope.
#[derive(Debug, derive_more::Error, derive_more::Display, Getters)]
#[display(
fmt = "Symbol [{}] was declared in scope [{}] multiple times.",
symbol_name,
scope_name
)]
#[getset(get = "pub")]
pub struct DeclareExistingSymbolError {
    scope_name: String,
    symbol_name: String,
}

impl DeclareExistingSymbolError {
    pub fn new(scope_name: String, symbol_name: String) -> Self {
        DeclareExistingSymbolError {
            scope_name,
            symbol_name,
        }
    }
}

/// Type to represent errors originating
/// from usage of undeclared symbols.
#[derive(Debug, derive_more::Error, derive_more::Display, Getters)]
#[display(
fmt = "Symbol [{}], declaration not found in scope [{}].",
symbol_name,
scope_name
)]
#[getset(get = "pub")]
pub struct UseUndeclaredSymbolError {
    scope_name: String,
    symbol_name: String,
}

impl UseUndeclaredSymbolError {
    pub fn new(scope_name: String, symbol_name: String) -> Self {
        UseUndeclaredSymbolError {
            scope_name,
            symbol_name,
        }
    }
}

/// Type representing possible errors
/// that can happen while using symbols
#[derive(Debug, derive_more::Error, derive_more::Display)]
pub enum SymbolError {
    DeclareExistingSymbol(DeclareExistingSymbolError),
    UseUndeclaredSymbol(UseUndeclaredSymbolError),
}