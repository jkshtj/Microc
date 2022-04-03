use crate::symbol_table::error::{DeclareExistingSymbolError, UseUndeclaredSymbolError, DeclareInInvalidScopeError, SymbolError, ScopeType};
use crate::symbol_table::symbol::data;
use crate::symbol_table::symbol::function;
use linked_hash_set::LinkedHashSet;
use linked_hash_map::LinkedHashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};
use crate::symbol_table::SYMBOL_TABLE;
use std::cell::RefCell;
use std::panic::panic_any;

static STACK_FRAME_LOCAL_SLOT_COUNTER: AtomicU32 = AtomicU32::new(1);
static STACK_FRAME_PARAM_SLOT_COUNTER: AtomicU32 = AtomicU32::new(1);

pub fn reset_stack_frame_local_slot_counter() {
    STACK_FRAME_LOCAL_SLOT_COUNTER.store(1, Ordering::SeqCst);
}

pub fn get_stack_frame_local_slot_counter() -> u32 {
    STACK_FRAME_LOCAL_SLOT_COUNTER.load(Ordering::SeqCst)
}

pub fn reset_stack_frame_param_slot_counter() {
    STACK_FRAME_PARAM_SLOT_COUNTER.store(1, Ordering::SeqCst);
}

pub fn get_stack_frame_param_slot_counter() -> u32 {
    STACK_FRAME_PARAM_SLOT_COUNTER.load(Ordering::SeqCst)
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Scope {
    Global {
        data_symbols: LinkedHashSet<Rc<data::NonFunctionScopedSymbol>>,
        function_symbols: LinkedHashSet<Rc<function::Symbol>>,
    },
    Anonymous {
        name: String,
        parent: Rc<RefCell<Scope>>,
        data_symbols: LinkedHashSet<Rc<data::NonFunctionScopedSymbol>>,
    },
    Function {
        name: String,
        parent: Rc<RefCell<Scope>>,
        data_symbols: LinkedHashMap<String, Rc<data::FunctionScopedSymbol>>,
    },
}

impl Display for Scope {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Scope::Global { data_symbols, .. } => {
                writeln!(f, "Symbol table GLOBAL")?;
                data_symbols
                    .iter()
                    .try_for_each(|symbol| writeln!(f, "{}", symbol))?;
            }
            Scope::Anonymous {
                name, data_symbols, ..
            } => {
                writeln!(f, "Symbol table {}", self.name())?;
                data_symbols
                    .iter()
                    .try_for_each(|symbol| writeln!(f, "{}", symbol))?;
            }
            Scope::Function {
                name, data_symbols, ..
            } => {
                writeln!(f, "Symbol table {}", self.name())?;
                data_symbols
                    .iter()
                    .try_for_each(|(name, symbol)| writeln!(f, "{} : {}", name, symbol))?;
            }
        }
        Ok(())
    }
}

impl Scope {
    pub(crate) fn new_global() -> Self {
        Self::Global {
            data_symbols: LinkedHashSet::new(),
            function_symbols: LinkedHashSet::new(),
        }
    }

    pub(crate) fn new_anonymous<T: ToString>(name: T, parent: Rc<RefCell<Scope>>) -> Self {
        Self::Anonymous {
            name: name.to_string(),
            parent,
            data_symbols: LinkedHashSet::new(),
        }
    }

    pub(crate) fn new_function<T: ToString>(name: T, parent: Rc<RefCell<Scope>>) -> Self {
        Self::Function {
            name: name.to_string(),
            parent,
            data_symbols: LinkedHashMap::new(),
        }
    }

    pub(crate) fn name(&self) -> &str {
        match self {
            Scope::Global { .. } => "GLOBAL",
            Scope::Anonymous { name, .. } | Scope::Function { name, .. } => name,
        }
    }

    pub(crate) fn add_function_symbol(
        &mut self,
        symbol: function::Symbol,
    ) -> Result<(), SymbolError> {
        if self.contains_function_symbol(&symbol) {
            return Err(SymbolError::DeclareExistingSymbol(
                DeclareExistingSymbolError::new(
                    self.name().to_owned(),
                    symbol.name().to_owned(),
                ))
            );
        }

        match self {
            Scope::Anonymous { .. } | Scope::Function { .. } => {
                let scope_type = if let Scope::Anonymous { .. } = self {
                    ScopeType::Anonymous
                } else {
                    ScopeType::Function
                };

                return Err(SymbolError::DeclareInInvalidSymbolScope(
                    DeclareInInvalidScopeError::new(
                        self.name().to_owned(),
                        scope_type,
                        symbol.name().to_owned(),
                    ))
                );
            }
            Scope::Global {function_symbols, ..} => function_symbols.insert(Rc::new(symbol)),
        };

        Ok(())
    }

    pub(crate) fn add_non_func_scoped_symbol(
        &mut self,
        symbol: data::NonFunctionScopedSymbol,
    ) -> Result<(), SymbolError> {
        if self.contains_non_func_scoped_symbol(&symbol) {
            return Err(SymbolError::DeclareExistingSymbol(
                DeclareExistingSymbolError::new(
                    self.name().to_owned(),
                    symbol.name().to_owned(),
                ))
            );
        }

        match self {
            Scope::Function { .. } => {
                return Err(SymbolError::DeclareInInvalidSymbolScope(
                    DeclareInInvalidScopeError::new(
                        self.name().to_owned(),
                        ScopeType::Function,
                        symbol.name().to_owned(),
                    ))
                );
            }
            Scope::Global { data_symbols, .. } | Scope::Anonymous { data_symbols, .. } => data_symbols.insert(Rc::new(symbol)),
        };

        Ok(())
    }

    pub(crate) fn add_func_scoped_symbol(
        &mut self,
        name: String,
        symbol: data::FunctionScopedSymbol,
    ) -> Result<(), SymbolError> {
        if self.contains_func_scoped_symbol(&name) {
            return Err(SymbolError::DeclareExistingSymbol(
                DeclareExistingSymbolError::new(
                    self.name().to_owned(),
                    name,
                ))
            );
        }

        match self {
            Scope::Global { .. } | Scope::Anonymous { .. } => {
                let scope_type = if let Scope::Anonymous { .. } = self {
                    ScopeType::Anonymous
                } else {
                    ScopeType::Global
                };

                return Err(SymbolError::DeclareInInvalidSymbolScope(
                    DeclareInInvalidScopeError::new(
                        self.name().to_owned(),
                        scope_type,
                        name,
                    ))
                );
            }
            Scope::Function {
                data_symbols,
                ..
            } => data_symbols.insert(name, Rc::new(symbol)),
        };
        Ok(())
    }

    /// Recursively searches for a data symbol
    /// in all scopes starting from current scope and
    /// going up the ancestral chain, all the way up to
    /// the global scope.
    pub(crate) fn data_symbol_for_name(
        &self,
        symbol_name: &str,
    ) -> Result<data::Symbol, SymbolError> {
        match self {
            Scope::Global { data_symbols, .. } => data_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| data::Symbol::NonFunctionScopedSymbol(symbol.clone()))
                .ok_or(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                    symbol_name.to_owned(),
                ))),
            Scope::Anonymous { data_symbols, parent, .. } => data_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map_or_else(
                    || parent.borrow().data_symbol_for_name(symbol_name),
                    |symbol| Ok(data::Symbol::NonFunctionScopedSymbol(symbol.clone()))
                ),
            Scope::Function { data_symbols, parent, .. } => data_symbols
                .iter()
                .find(|&(name, symbol)| name == symbol_name)
                .map_or_else(
                    || parent.borrow().data_symbol_for_name(symbol_name),
                    |(name, symbol)| Ok(data::Symbol::FunctionScopedSymbol(symbol.clone()))
                ),
        }
    }

    pub(crate) fn function_symbol_for_name(
        &self,
        symbol_name: &str,
    ) -> Result<Rc<function::Symbol>, SymbolError> {
        match self {
            Scope::Global {
                function_symbols, ..
            } => function_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| symbol.clone())
                .ok_or(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                    symbol_name.to_owned(),
                ))),
            Scope::Anonymous { .. } | Scope::Function { .. } => Err(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                symbol_name.to_owned(),
            ))),
        }
    }

    fn contains_non_func_scoped_symbol(&self, symbol: &data::NonFunctionScopedSymbol) -> bool {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. } => data_symbols.contains(symbol),
            _ => false
        }
    }

    fn contains_func_scoped_symbol(&self, name: &str) -> bool {
        match self {
            Scope::Function {data_symbols, ..} => data_symbols.contains_key(name),
            _ => false,
        }
    }

    fn contains_function_symbol(&self, symbol: &function::Symbol) -> bool {
        match self {
            Scope::Global {
                function_symbols, ..
            } => function_symbols.contains(symbol),
            _ => false,
        }
    }

    #[cfg(test)]
    pub(crate) fn parent(&self) -> Rc<RefCell<Scope>> {
        match self {
            Scope::Global { .. } => panic!("Global scope does not have a parent!"),
            Scope::Anonymous { parent, .. }
            | Scope::Function { parent, .. } => Rc::clone(parent)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::symbol_table::symbol::function::ReturnType;
    use crate::symbol_table::error::ScopeType::Anonymous;
    use crate::symbol_table::symbol::data::FunctionScopedSymbolType;

    #[test]
    fn scope_name_set_correctly() {
        let global = Rc::new(RefCell::new(Scope::new_global()));
        let anonymous = Scope::new_anonymous("Anonymous", Rc::clone(&global));
        let function = Scope::new_function("Function", Rc::clone(&global));
        assert_eq!("GLOBAL", global.borrow().name());
        assert_eq!("Anonymous", anonymous.name());
        assert_eq!("Function", function.name());
    }

    #[test]
    fn add_func_symbol_under_invalid_scope_returns_invalid_scope_declaration_error() {
        let symbol = function::Symbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![],
            vec![],
        );

        let global = Rc::new(RefCell::new(Scope::new_global()));
        let mut anonymous = Scope::new_anonymous("Anonymous", global);
        assert_eq!(SymbolError::DeclareInInvalidSymbolScope(DeclareInInvalidScopeError::new(
            "Anonymous".to_owned(),
            ScopeType::Anonymous,
            "some_func".to_string()
            )), anonymous.add_function_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_existing_func_symbol_under_valid_scope_returns_symbol_redeclaration_error() {
        let symbol = function::Symbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![],
            vec![],
        );

        let mut global = Scope::new_global();
        global.add_function_symbol(symbol.clone());
        assert_eq!(SymbolError::DeclareExistingSymbol(DeclareExistingSymbolError::new(
            "GLOBAL".to_owned(),
            "some_func".to_string()
        )), global.add_function_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_non_func_scoped_symbol_under_invalid_scope_returns_invalid_scope_declaration_error() {
        let symbol = data::NonFunctionScopedSymbol::Int {
            name: "symbol".to_owned(),
        };
        let global = Rc::new(RefCell::new(Scope::new_global()));
        let mut function = Scope::new_function("Function", global);
        assert_eq!(SymbolError::DeclareInInvalidSymbolScope(DeclareInInvalidScopeError::new(
            "Function".to_owned(),
            ScopeType::Function,
            "symbol".to_string()
        )), function.add_non_func_scoped_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_existing_non_func_scoped_symbol_under_valid_scope_returns_symbol_redeclaration_error() {
        let symbol = data::NonFunctionScopedSymbol::Int {
            name: "symbol".to_owned(),
        };

        let mut global = Scope::new_global();
        global.add_non_func_scoped_symbol(symbol.clone());
        assert_eq!(SymbolError::DeclareExistingSymbol(DeclareExistingSymbolError::new(
            "GLOBAL".to_owned(),
            "symbol".to_string()
        )), global.add_non_func_scoped_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_func_scoped_symbol_under_invalid_scope_returns_invalid_scope_declaration_error() {
        let symbol = data::FunctionScopedSymbol::Int {
            symbol_type: FunctionScopedSymbolType::Local,
            index: 42,
        };
        let global = Rc::new(RefCell::new(Scope::new_global()));
        let mut anonymous = Scope::new_anonymous("Anonymous", global);
        assert_eq!(SymbolError::DeclareInInvalidSymbolScope(DeclareInInvalidScopeError::new(
            "Anonymous".to_owned(),
            ScopeType::Anonymous,
            "symbol".to_string()
        )), anonymous.add_func_scoped_symbol("symbol".to_owned(), symbol).unwrap_err());
    }

    #[test]
    fn add_existing_func_scoped_symbol_under_valid_scope_returns_symbol_redeclaration_error() {
        let symbol = data::FunctionScopedSymbol::Int {
            symbol_type: FunctionScopedSymbolType::Local,
            index: 42,
        };

        let global = Rc::new(RefCell::new(Scope::new_global()));
        let mut function = Scope::new_function("Function", global);
        function.add_func_scoped_symbol("symbol".to_owned(), symbol.clone());
        assert_eq!(SymbolError::DeclareExistingSymbol(DeclareExistingSymbolError::new(
            "Function".to_owned(),
            "symbol".to_string()
        )), function.add_func_scoped_symbol("symbol".to_owned(), symbol).unwrap_err());
    }

    #[test]
    fn non_func_scoped_symbol_for_name_returns_symbol_when_symbol_and_scope_valid() {
        let symbol = data::NonFunctionScopedSymbol::Int {
            name: "symbol".to_owned(),
        };
        let mut global = Scope::new_global();
        global.add_non_func_scoped_symbol(symbol.clone());
        let symbol = Rc::new(symbol);
        matches!(global.data_symbol_for_name("symbol").unwrap(), data::Symbol::NonFunctionScopedSymbol(symbol));
    }

    #[test]
    fn non_func_scoped_symbol_for_name_returns_undeclared_symbol_error_when_symbol_undeclared() {
        let symbol = data::NonFunctionScopedSymbol::Int {
            name: "symbol".to_owned(),
        };
        let mut global = Scope::new_global();
        assert_eq!(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
            "symbol".to_owned()
        )), global.data_symbol_for_name("symbol").unwrap_err());
    }

    #[test]
    fn func_scoped_symbol_for_name_returns_symbol_when_symbol_and_scope_valid() {
        let symbol = data::FunctionScopedSymbol::Int {
            symbol_type: FunctionScopedSymbolType::Local,
            index: 42,
        };
        let global = Rc::new(RefCell::new(Scope::new_global()));
        let mut function = Scope::new_function("Function", global);
        function.add_func_scoped_symbol("symbol".to_owned(), symbol.clone());
        let symbol = Rc::new(symbol);
        matches!(function.data_symbol_for_name("symbol").unwrap(), data::Symbol::FunctionScopedSymbol(symbol));
    }

    #[test]
    fn func_scoped_symbol_for_name_returns_undeclared_symbol_error_when_symbol_undeclared() {
        let symbol = data::FunctionScopedSymbol::Int {
            symbol_type: FunctionScopedSymbolType::Local,
            index: 42,
        };
        let global = Rc::new(RefCell::new(Scope::new_global()));
        let mut function = Scope::new_function("Function", global);
        assert_eq!(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
            "symbol".to_owned()
        )), function.data_symbol_for_name("symbol").unwrap_err());
    }


    #[test]
    fn data_symbol_for_name_looks_recursively_through_scope_hierarchy() {
        let symbol = data::NonFunctionScopedSymbol::Int {
            name: "symbol".to_owned(),
        };

        let global = Rc::new(RefCell::new(Scope::new_global()));

        // Symbol is added under the global scope
        global.borrow_mut().add_non_func_scoped_symbol(symbol.clone());

        let mut function = Scope::new_function("Function", global);
        let symbol = Rc::new(symbol);
        // Yet it will be resolvable from a function scope which is a child of the global scope
        matches!(function.data_symbol_for_name("symbol").unwrap(), data::Symbol::NonFunctionScopedSymbol(symbol));
    }

    #[test]
    fn func_symbol_for_name_returns_symbol_when_symbol_and_scope_valid() {
        let symbol = function::Symbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![],
            vec![],
        );
        let mut global = Scope::new_global();
        global.add_function_symbol(symbol.clone());
        assert_eq!(symbol, *global.function_symbol_for_name("some_func").unwrap());
    }

    #[test]
    fn func_symbol_for_name_returns_undeclared_symbol_error_when_symbol_undeclared() {
        let symbol = function::Symbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![],
            vec![],
        );
        let mut global = Scope::new_global();
        assert_eq!(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
            "some_func".to_owned()
        )), global.function_symbol_for_name("some_func").unwrap_err());
    }
}
