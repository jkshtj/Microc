use crate::symbol_table::error::{DeclareExistingSymbolError, UseUndeclaredSymbolError, DeclareInInvalidScopeError, SymbolError, ScopeType};
use crate::symbol_table::symbol::data::{DataSymbol, FunctionDataSymbol};
use crate::symbol_table::symbol::function::FunctionSymbol;
use linked_hash_set::LinkedHashSet;
use linked_hash_map::LinkedHashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};

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

#[derive(Debug)]
pub(crate) enum Scope {
    Global {
        data_symbols: LinkedHashSet<Rc<DataSymbol>>,
        function_symbols: LinkedHashSet<Rc<FunctionSymbol>>,
    },
    Anonymous {
        name: String,
        parent_id: Option<usize>,
        data_symbols: LinkedHashSet<Rc<DataSymbol>>,
    },
    Function {
        name: String,
        parent_id: Option<usize>,
        data_symbols: LinkedHashMap<String, Rc<FunctionDataSymbol>>,
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

    pub(crate) fn new_anonymous<T: ToString>(name: T, parent_id: Option<usize>) -> Self {
        Self::Anonymous {
            name: name.to_string(),
            parent_id,
            data_symbols: LinkedHashSet::new(),
        }
    }

    pub(crate) fn new_function<T: ToString>(name: T, parent_id: Option<usize>) -> Self {
        Self::Function {
            name: name.to_string(),
            parent_id,
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
        symbol: FunctionSymbol,
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

    pub(crate) fn add_data_symbol(
        &mut self,
        symbol: DataSymbol,
    ) -> Result<(), SymbolError> {
        if self.contains_data_symbol(&symbol) {
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

    pub(crate) fn add_func_data_symbol(
        &mut self,
        name: String,
        symbol: FunctionDataSymbol,
    ) -> Result<(), SymbolError> {
        if self.contains_func_data_symbol(&name) {
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

    pub(crate) fn data_symbol_for_name(
        &self,
        symbol_name: &str,
    ) -> Result<Rc<DataSymbol>, SymbolError> {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. } => data_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| symbol.clone())
                .ok_or(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                    self.name().to_owned(),
                    symbol_name.to_owned(),
                ))),
            _ => Err(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                self.name().to_owned(),
                symbol_name.to_owned(),
            ))),
        }
    }

    pub(crate) fn func_data_symbol_for_name(
        &self,
        symbol_name: &str,
    ) -> Result<Rc<FunctionDataSymbol>, SymbolError> {
        match self {
            Scope::Function { data_symbols, .. } => data_symbols
                .iter()
                .find(|(name, symbol)| name.as_str() == symbol_name)
                .map(|(name, symbol)| symbol.clone())
                .ok_or(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                    self.name().to_owned(),
                    symbol_name.to_owned(),
                ))),
            _ => Err(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                self.name().to_owned(),
                symbol_name.to_owned(),
            ))),
        }
    }

    pub(crate) fn function_symbol_for_name(
        &self,
        symbol_name: &str,
    ) -> Result<Rc<FunctionSymbol>, SymbolError> {
        match self {
            Scope::Global {
                function_symbols, ..
            } => function_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| symbol.clone())
                .ok_or(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                    self.name().to_owned(),
                    symbol_name.to_owned(),
                ))),
            Scope::Anonymous { .. } | Scope::Function { .. } => Err(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
                self.name().to_owned(),
                symbol_name.to_owned(),
            ))),
        }
    }

    fn contains_data_symbol(&self, symbol: &DataSymbol) -> bool {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. } => data_symbols.contains(symbol),
            _ => false
        }
    }

    fn contains_func_data_symbol(&self, name: &str) -> bool {
        match self {
            Scope::Function {data_symbols, ..} => data_symbols.contains_key(name),
            _ => false,
        }
    }

    fn contains_function_symbol(&self, symbol: &FunctionSymbol) -> bool {
        match self {
            Scope::Global {
                function_symbols, ..
            } => function_symbols.contains(symbol),
            _ => false,
        }
    }

    #[cfg(test)]
    pub(crate) fn parent_id(&self) -> Option<usize> {
        match self {
            Scope::Global { .. } => None,
            Scope::Anonymous { parent_id, .. } | Scope::Function { parent_id, .. } => {
                parent_id.as_ref().copied()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::symbol_table::symbol::function::ReturnType;
    use crate::symbol_table::error::ScopeType::Anonymous;
    use crate::symbol_table::symbol::data::FunctionDataSymbolType;

    #[test]
    fn scope_name_set_correctly() {
        let global = Scope::new_global();
        let anonymous = Scope::new_anonymous("Anonymous", None);
        let function = Scope::new_function("Function", None);
        assert_eq!("GLOBAL", global.name());
        assert_eq!("Anonymous", anonymous.name());
        assert_eq!("Function", function.name());
    }

    #[test]
    fn add_func_symbol_under_invalid_scope_returns_invalid_scope_declaration_error() {
        let symbol = FunctionSymbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![]
        );

        let mut anonymous = Scope::new_anonymous("Anonymous", None);
        assert_eq!(SymbolError::DeclareInInvalidSymbolScope(DeclareInInvalidScopeError::new(
            "Anonymous".to_owned(),
            ScopeType::Anonymous,
            "some_func".to_string()
            )), anonymous.add_function_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_existing_func_symbol_under_valid_scope_returns_symbol_redeclaration_error() {
        let symbol = FunctionSymbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![]
        );

        let mut global = Scope::new_global();
        global.add_function_symbol(symbol.clone());
        assert_eq!(SymbolError::DeclareExistingSymbol(DeclareExistingSymbolError::new(
            "GLOBAL".to_owned(),
            "some_func".to_string()
        )), global.add_function_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_data_symbol_under_invalid_scope_returns_invalid_scope_declaration_error() {
        let symbol = DataSymbol::Int {
            name: "symbol".to_owned(),
        };

        let mut function = Scope::new_function("Function", None);
        assert_eq!(SymbolError::DeclareInInvalidSymbolScope(DeclareInInvalidScopeError::new(
            "Function".to_owned(),
            ScopeType::Function,
            "symbol".to_string()
        )), function.add_data_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_existing_data_symbol_under_valid_scope_returns_symbol_redeclaration_error() {
        let symbol = DataSymbol::Int {
            name: "symbol".to_owned(),
        };

        let mut global = Scope::new_global();
        global.add_data_symbol(symbol.clone());
        assert_eq!(SymbolError::DeclareExistingSymbol(DeclareExistingSymbolError::new(
            "GLOBAL".to_owned(),
            "symbol".to_string()
        )), global.add_data_symbol(symbol).unwrap_err());
    }

    #[test]
    fn add_func_data_symbol_under_invalid_scope_returns_invalid_scope_declaration_error() {
        let symbol = FunctionDataSymbol::Int {
            symbol_type: FunctionDataSymbolType::Local,
            index: 42,
        };

        let mut anonymous = Scope::new_anonymous("Anonymous", None);
        assert_eq!(SymbolError::DeclareInInvalidSymbolScope(DeclareInInvalidScopeError::new(
            "Anonymous".to_owned(),
            ScopeType::Anonymous,
            "symbol".to_string()
        )), anonymous.add_func_data_symbol("symbol".to_owned(), symbol).unwrap_err());
    }

    #[test]
    fn add_existing_func_data_symbol_under_valid_scope_returns_symbol_redeclaration_error() {
        let symbol = FunctionDataSymbol::Int {
            symbol_type: FunctionDataSymbolType::Local,
            index: 42,
        };

        let mut function = Scope::new_function("Function", None);
        function.add_func_data_symbol("symbol".to_owned(), symbol.clone());
        assert_eq!(SymbolError::DeclareExistingSymbol(DeclareExistingSymbolError::new(
            "Function".to_owned(),
            "symbol".to_string()
        )), function.add_func_data_symbol("symbol".to_owned(), symbol).unwrap_err());
    }

    #[test]
    fn data_symbol_for_name_returns_symbol_when_symbol_and_scope_valid() {
        let symbol = DataSymbol::Int {
            name: "symbol".to_owned(),
        };
        let mut global = Scope::new_global();
        global.add_data_symbol(symbol.clone());
        assert_eq!(symbol, *global.data_symbol_for_name("symbol").unwrap());
    }

    #[test]
    fn data_symbol_for_name_returns_undeclared_symbol_error_when_symbol_undeclared() {
        let symbol = DataSymbol::Int {
            name: "symbol".to_owned(),
        };
        let mut global = Scope::new_global();
        assert_eq!(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
            "GLOBAL".to_owned(),
            "symbol".to_owned()
        )), global.data_symbol_for_name("symbol").unwrap_err());
    }

    #[test]
    fn func_data_symbol_for_name_returns_symbol_when_symbol_and_scope_valid() {
        let symbol = FunctionDataSymbol::Int {
            symbol_type: FunctionDataSymbolType::Local,
            index: 42,
        };
        let mut function = Scope::new_function("Function", None);
        function.add_func_data_symbol("symbol".to_owned(), symbol.clone());
        assert_eq!(symbol, *function.func_data_symbol_for_name("symbol").unwrap());
    }

    #[test]
    fn func_data_symbol_for_name_returns_undeclared_symbol_error_when_symbol_undeclared() {
        let symbol = FunctionDataSymbol::Int {
            symbol_type: FunctionDataSymbolType::Local,
            index: 42,
        };
        let mut function = Scope::new_function("Function", None);
        assert_eq!(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
            "Function".to_owned(),
            "symbol".to_owned()
        )), function.func_data_symbol_for_name("symbol").unwrap_err());
    }

    #[test]
    fn func_symbol_for_name_returns_symbol_when_symbol_and_scope_valid() {
        let symbol = FunctionSymbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![]
        );
        let mut global = Scope::new_global();
        global.add_function_symbol(symbol.clone());
        assert_eq!(symbol, *global.function_symbol_for_name("some_func").unwrap());
    }

    #[test]
    fn func_symbol_for_name_returns_undeclared_symbol_error_when_symbol_undeclared() {
        let symbol = FunctionSymbol::new(
            "some_func".to_owned(),
            ReturnType::Void,
            vec![]
        );
        let mut global = Scope::new_global();
        assert_eq!(SymbolError::UseUndeclaredSymbol(UseUndeclaredSymbolError::new(
            "GLOBAL".to_owned(),
            "some_func".to_owned()
        )), global.function_symbol_for_name("some_func").unwrap_err());
    }
}
