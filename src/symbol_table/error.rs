use getset::Getters;

/// Type to represent errors originating
/// from multiple symbol declarations with
/// the same name in the same scope.
#[derive(Debug, derive_more::Error, derive_more::Display, Getters, Eq, PartialEq, Clone)]
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
#[derive(Debug, derive_more::Error, derive_more::Display, Getters, Eq, PartialEq, Clone)]
#[display(
    fmt = "Use of undeclared symbol: [{}].",
    symbol_name,
)]
#[getset(get = "pub")]
pub struct UseUndeclaredSymbolError {
    symbol_name: String,
}

impl UseUndeclaredSymbolError {
    pub fn new(symbol_name: String) -> Self {
        UseUndeclaredSymbolError {
            symbol_name,
        }
    }
}

#[derive(Debug, derive_more::Display, Eq, PartialEq, Clone)]
pub enum ScopeType {
    Global,
    Anonymous,
    Function
}

/// Type to represent errors originating from declaring
/// symbols in contextually invalid scopes - globals
/// cannot be declared in functions, parameters cannot be
/// declared outside of functions etc.
#[derive(Debug, derive_more::Error, derive_more::Display, Getters, Eq, PartialEq, Clone)]
#[display(
    fmt = "Symbol [{}], cannot be declared in scope with name: [{}] and type: [{}].",
    symbol_name,
    scope_name,
    scope_type,
)]
#[getset(get = "pub")]
pub struct DeclareInInvalidScopeError {
    scope_name: String,
    scope_type: ScopeType,
    symbol_name: String,
}

impl DeclareInInvalidScopeError {
    pub fn new(scope_name: String, scope_type: ScopeType, symbol_name: String) -> Self {
        Self {
            scope_name,
            scope_type,
            symbol_name,
        }
    }
}

/// Type representing possible errors
/// that can happen while using symbols
#[derive(Debug, derive_more::Error, derive_more::Display, PartialEq, Eq, Clone)]
pub enum SymbolError {
    /// User tries to declare multiple symbols with
    /// the same name in the same scope
    DeclareExistingSymbol(DeclareExistingSymbolError),
    /// User tries to use an undeclared symbol
    UseUndeclaredSymbol(UseUndeclaredSymbolError),
    /// User tries to declare symbols in an invalid
    /// scope. For instance, functions are the only
    /// scope where parameter symbols can be declared.
    DeclareInInvalidSymbolScope(DeclareInInvalidScopeError)
}
