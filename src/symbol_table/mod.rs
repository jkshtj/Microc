#![allow(unused)]

use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};

use atomic_refcell::AtomicRefCell;
use getset::Getters;

use crate::symbol_table::decl::{FloatDecl, IntDecl, StringDecl};
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};

pub mod decl;

// NOTE - This global, static symbol table requires
// and assumes the compiler to be single threaded.
lazy_static::lazy_static! {
    pub static ref SYMBOL_TABLE: AtomicRefCell<SymbolTable> = AtomicRefCell::new(SymbolTable::Active(ScopeTree::new()));
}

static ANONYMOUS_SCOPE_COUNTER: AtomicU32 = AtomicU32::new(1);
static STACK_FRAME_LOCAL_SLOT_COUNTER: AtomicI32 = AtomicI32::new(0);
static STACK_FRAME_PARAM_SLOT_COUNTER: AtomicU32 = AtomicU32::new(0);

pub fn init_stack_frame_local_slot_counter(n: i32) {
    STACK_FRAME_LOCAL_SLOT_COUNTER.store(n, Ordering::SeqCst);
}

pub fn reset_stack_frame_local_slot_counter() {
    STACK_FRAME_LOCAL_SLOT_COUNTER.store(0, Ordering::SeqCst);
}

pub fn init_stack_frame_param_slot_counter(n: u32) {
    STACK_FRAME_PARAM_SLOT_COUNTER.store(n, Ordering::SeqCst);
}

pub fn reset_stack_frame_param_slot_counter() {
    STACK_FRAME_PARAM_SLOT_COUNTER.store(0, Ordering::SeqCst);
}

/// Type to represent errors originating
/// from use of undeclared symbols.
#[derive(Debug, derive_more::Error, derive_more::Display, Getters)]
#[display(
    fmt = "Symbol [{}] was declared in scope [{}] multiple times.",
    symbol_name,
    scope_name
)]
#[getset(get = "pub")]
pub struct DeclarationError {
    scope_name: String,
    symbol_name: String,
}

impl DeclarationError {
    pub fn new(scope_name: String, symbol_name: String) -> Self {
        DeclarationError {
            scope_name,
            symbol_name,
        }
    }
}

/// Global symbol table that either
/// represents a scope tree or an
/// inactive symbol table that can
/// neither be read or modified.
pub enum SymbolTable {
    Active(ScopeTree),
    Sealed,
}

impl SymbolTable {
    // TODO: Do we need a symbol table iterator that
    // allows us to iterate through symbols without
    // consuming the symbol table?
    /// Seals the symbol table and
    /// returns the current symbols.
    pub fn seal() -> Vec<Symbol> {
        let mut symbol_table = SYMBOL_TABLE.borrow_mut();
        if let SymbolTable::Active(ref mut scope_tree) = *symbol_table {
            let scopes = std::mem::take(&mut scope_tree.scopes);
            *symbol_table = SymbolTable::Sealed;
            scopes
                .into_iter()
                .flat_map(|scope| scope.into_symbols())
                .collect()
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    pub fn set_decl_error(decl_error: DeclarationError) {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            scope_tree.decl_error.replace(decl_error);
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    pub fn add_anonymous_scope() {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            let active_scope_id = scope_tree.active_scope_id();

            let anonymous_scope_name = format!(
                "BLOCK{}",
                ANONYMOUS_SCOPE_COUNTER.fetch_add(1, Ordering::SeqCst)
            );
            let new_scope = Scope::new_anonymous(anonymous_scope_name, Some(active_scope_id));
            scope_tree.scopes.push(new_scope);

            let new_scope_id = scope_tree.scopes.len() - 1;
            scope_tree.active_scope_stack.push(new_scope_id);
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    pub fn add_function_scope<T: ToString + Debug>(name: T) {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            let active_scope_id = scope_tree.active_scope_id();

            let new_scope = Scope::new_function(name, Some(active_scope_id));
            scope_tree.scopes.push(new_scope);

            let new_scope_id = scope_tree.scopes.len() - 1;
            scope_tree.active_scope_stack.push(new_scope_id);
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    pub fn end_curr_scope() {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            scope_tree.active_scope_stack.pop();
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    pub fn add_symbol<T: Into<Symbol> + Debug>(
        symbol: T,
        is_func_param: bool,
    ) -> Result<(), DeclarationError> {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            let active_scope = scope_tree.active_scope_mut();
            active_scope.add_symbol(symbol.into(), is_func_param)?;
        } else {
            panic!("Symbol table has been sealed.");
        }

        Ok(())
    }

    // TODO: Should this return a `Result`?
    pub fn symbol_type_for(symbol_name: &str) -> Option<SymbolType> {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let global_scope = scope_tree.global_scope();

            global_scope.symbol_type(symbol_name).or_else(|| {
                let active_scope = scope_tree.active_scope();
                active_scope.symbol_type(symbol_name)
            })
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    #[cfg(test)]
    fn print_symbol_table() {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            println!("{}", scope_tree);
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    #[cfg(test)]
    fn num_scopes() -> usize {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            scope_tree.scopes.len()
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    #[cfg(test)]
    fn curr_scope() -> usize {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            *scope_tree.active_scope_stack.last().unwrap()
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    #[cfg(test)]
    fn parent_of_scope(id: usize) -> Option<usize> {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let scope = scope_tree.scopes.get(id).unwrap();
            scope.parent_id()
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    #[cfg(test)]
    fn is_symbol_under(scope_id: usize, symbol: &Symbol) -> bool {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let scope = scope_tree.scopes.get(scope_id).unwrap();
            scope.symbols().contains(symbol)
        } else {
            panic!("Symbol table has been sealed.");
        }
    }

    #[cfg(test)]
    fn is_active_scope_name(name: &'static str) -> bool {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let active_scope_id = *scope_tree.active_scope_stack.last().unwrap();
            let curr_scope = scope_tree.scopes.get(active_scope_id).unwrap();
            curr_scope.name() == name
        } else {
            panic!("Symbol table has been sealed.");
        }
    }
}

/// A tree like structure for representing
/// scopes. Each scope uses one table of
/// symbols per scope.
#[derive(Debug)]
pub struct ScopeTree {
    scopes: Vec<Scope>,
    active_scope_stack: Vec<usize>,
    decl_error: Option<DeclarationError>,
}

impl Display for ScopeTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(decl_err) = &self.decl_error {
            writeln!(f, "DECLARATION ERROR {}", decl_err.symbol_name())?
        } else {
            self.scopes
                .iter()
                .try_for_each(|scope| writeln!(f, "{}", scope))?;
        }
        Ok(())
    }
}

impl ScopeTree {
    fn new() -> Self {
        Self {
            scopes: vec![Scope::new_global()],
            active_scope_stack: vec![0],
            decl_error: None,
        }
    }

    fn global_scope(&self) -> &Scope {
        // Unwrapping here should be safe as we never initialize a
        // symbol table without a global scope.
        self.scopes.first().unwrap()
    }

    fn global_scope_mut(&mut self) -> &mut Scope {
        // Unwrapping here should be safe as we never initialize a
        // symbol table without a global scope.
        self.scopes.first_mut().unwrap()
    }

    fn active_scope(&self) -> &Scope {
        // Unwrapping here should be safe as we never create a
        // SymbolTable without setting an active scope.
        let active_scope_id = *self.active_scope_stack.last().unwrap();

        // Unwrapping here should be safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        self.scopes.get(active_scope_id).unwrap()
    }

    fn active_scope_mut(&mut self) -> &mut Scope {
        // Unwrapping here should be safe as we never create a
        // SymbolTable without setting an active scope.
        let active_scope_id = *self.active_scope_stack.last().unwrap();

        // Unwrapping here should be safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        self.scopes.get_mut(active_scope_id).unwrap()
    }

    fn active_scope_id(&self) -> usize {
        // Unwrapping here should be safe as we never create a
        // SymbolTable without setting an active scope.
        *self.active_scope_stack.last().unwrap()
    }
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub enum NumType {
    Int,
    Float,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum SymbolType {
    String,
    Num(NumType),
}

#[derive(Debug)]
enum Scope {
    Global {
        symbols: Vec<Symbol>,
        symbol_set: HashSet<String>,
    },
    Anonymous {
        name: String,
        parent_id: Option<usize>,
        symbols: Vec<Symbol>,
        symbol_set: HashSet<String>,
    },
    Function {
        name: String,
        parent_id: Option<usize>,
        symbols: Vec<Symbol>,
        symbol_set: HashSet<String>,
        stack_frame_local_slot_map: HashMap<String, i32>,
        stack_frame_param_slot_map: HashMap<String, u32>,
    },
}

impl Display for Scope {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Scope::Global { symbols, .. } => {
                writeln!(f, "Symbol table GLOBAL")?;
                self.symbols()
                    .iter()
                    .try_for_each(|symbol| writeln!(f, "{}", symbol))?;
            }
            Scope::Anonymous { name, symbols, .. } | Scope::Function { name, symbols, .. } => {
                writeln!(f, "Symbol table {}", self.name())?;
                self.symbols()
                    .iter()
                    .try_for_each(|symbol| writeln!(f, "{}", symbol))?;
            }
        }
        Ok(())
    }
}

impl Scope {
    fn new_global() -> Self {
        Self::Global {
            symbols: vec![],
            symbol_set: HashSet::new(),
        }
    }

    fn new_anonymous<T: ToString>(name: T, parent_id: Option<usize>) -> Self {
        Self::Anonymous {
            name: name.to_string(),
            parent_id,
            symbols: vec![],
            symbol_set: HashSet::new(),
        }
    }

    fn new_function<T: ToString>(name: T, parent_id: Option<usize>) -> Self {
        Self::Function {
            name: name.to_string(),
            parent_id,
            symbols: vec![],
            symbol_set: HashSet::new(),
            stack_frame_local_slot_map: HashMap::new(),
            stack_frame_param_slot_map: HashMap::new(),
        }
    }

    fn add_symbol(&mut self, symbol: Symbol, is_func_param: bool) -> Result<(), DeclarationError> {
        let symbol_name = symbol.get_name();
        if self.contains_symbol(symbol_name) {
            return Err(DeclarationError::new(
                self.name().to_owned(),
                symbol_name.to_owned(),
            ));
        }

        match self {
            Scope::Global {
                symbols,
                symbol_set,
                ..
            }
            | Scope::Anonymous {
                symbols,
                symbol_set,
                ..
            } => {
                symbol_set.insert(symbol_name.to_owned());
                symbols.push(symbol);
            }
            Scope::Function {
                symbols,
                symbol_set,
                stack_frame_local_slot_map,
                stack_frame_param_slot_map,
                ..
            } => {
                symbol_set.insert(symbol_name.to_owned());
                if is_func_param {
                    stack_frame_param_slot_map.insert(
                        symbol_name.to_owned(),
                        STACK_FRAME_PARAM_SLOT_COUNTER.fetch_add(1, Ordering::SeqCst),
                    );
                } else {
                    stack_frame_local_slot_map.insert(
                        symbol_name.to_owned(),
                        STACK_FRAME_LOCAL_SLOT_COUNTER.fetch_sub(1, Ordering::SeqCst),
                    );
                }
                symbols.push(symbol);
            }
        };
        Ok(())
    }

    fn symbols(&self) -> &Vec<Symbol> {
        match self {
            Scope::Global { symbols, .. }
            | Scope::Anonymous { symbols, .. }
            | Scope::Function { symbols, .. } => symbols,
        }
    }

    fn into_symbols(self) -> Vec<Symbol> {
        match self {
            Scope::Global { symbols, .. }
            | Scope::Anonymous { symbols, .. }
            | Scope::Function { symbols, .. } => symbols,
        }
    }

    fn name(&self) -> &str {
        match self {
            Scope::Global { .. } => "GLOBAL",
            Scope::Anonymous { name, .. } | Scope::Function { name, .. } => name,
        }
    }

    // TODO: Should this return a `Result`?
    fn symbol_type(&self, symbol_name: &str) -> Option<SymbolType> {
        match self {
            Scope::Global { symbols, .. }
            | Scope::Anonymous { symbols, .. }
            | Scope::Function { symbols, .. } => symbols
                .iter()
                .find(|&symbol| symbol.get_name() == symbol_name)
                .map(|symbol| match symbol {
                    Symbol::String(_) => SymbolType::String,
                    Symbol::Int(_) => SymbolType::Num(NumType::Int),
                    Symbol::Float(_) => SymbolType::Num(NumType::Float),
                }),
        }
    }

    fn contains_symbol(&self, symbol_name: &str) -> bool {
        match self {
            Scope::Global { symbol_set, .. }
            | Scope::Anonymous { symbol_set, .. }
            | Scope::Function { symbol_set, .. } => symbol_set.contains(symbol_name),
        }
    }

    #[cfg(test)]
    fn parent_id(&self) -> Option<usize> {
        match self {
            Scope::Global { .. } => None,
            Scope::Anonymous { parent_id, .. } | Scope::Function { parent_id, .. } => {
                parent_id.as_ref().copied()
            }
        }
    }
}

/// Represents a string, int or a float
/// symbol declared in the program.
#[derive(Debug, PartialEq, Clone, derive_more::Display)]
pub enum Symbol {
    #[display(fmt = "{}", _0)]
    String(StringDecl),
    #[display(fmt = "{}", _0)]
    Int(IntDecl),
    #[display(fmt = "{}", _0)]
    Float(FloatDecl),
}

impl Symbol {
    pub fn get_name(&self) -> &str {
        match self {
            Symbol::String(decl) => decl.get_name(),
            Symbol::Int(decl) => decl.get_name(),
            Symbol::Float(decl) => decl.get_name(),
        }
    }
}

#[cfg(test)]
mod test {
    // Symbol table does not support
    // concurrent modification.
    use serial_test::serial;

    use crate::symbol_table::SymbolType;
    use crate::token::{Token, TokenType};

    use super::*;

    fn setup() {
        let mut symbol_table = SYMBOL_TABLE.borrow_mut();
        if let SymbolTable::Active(ref mut scope_tree) = *symbol_table {
            *scope_tree = ScopeTree::new();
        } else {
            *symbol_table = SymbolTable::Active(ScopeTree::new());
        }
    }

    #[test]
    #[serial]
    fn symbol_table_active_on_first_access() {
        setup();
        assert!(matches!(*SYMBOL_TABLE.borrow(), SymbolTable::Active(_)));
    }

    #[test]
    #[serial]
    fn add_scope_works() {
        setup();

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(2, SymbolTable::num_scopes());

        let curr_scope = SymbolTable::curr_scope();
        assert_eq!(Some(0), SymbolTable::parent_of_scope(curr_scope));
    }

    #[test]
    #[serial]
    fn add_anonymous_scope_works() {
        setup();

        assert!(SymbolTable::is_active_scope_name("GLOBAL"));

        SymbolTable::add_anonymous_scope();
        // Num scopes
        assert_eq!(2, SymbolTable::num_scopes());
        // Anonymous scope names
        assert!(SymbolTable::is_active_scope_name("BLOCK1"));
        let curr_scope = SymbolTable::curr_scope();
        // Scope parents
        assert_eq!(Some(0), SymbolTable::parent_of_scope(curr_scope));

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(3, SymbolTable::num_scopes());
        assert!(SymbolTable::is_active_scope_name("ChildOfGlobal"));
        let curr_scope = SymbolTable::curr_scope();
        assert_eq!(Some(1), SymbolTable::parent_of_scope(curr_scope));

        SymbolTable::add_anonymous_scope();
        // Num scopes
        assert_eq!(4, SymbolTable::num_scopes());
        // Anonymous scope names
        assert!(SymbolTable::is_active_scope_name("BLOCK2"));
        let curr_scope = SymbolTable::curr_scope();
        // Scope parents
        assert_eq!(Some(2), SymbolTable::parent_of_scope(curr_scope));
    }

    #[test]
    #[serial]
    fn add_symbol_works() {
        setup();

        let symbol_under_global = Symbol::String(StringDecl::new(
            "global_symbol".to_owned(),
            "value1".to_owned(),
        ));

        // Should be added under "GLOBAL" scope
        SymbolTable::add_symbol(symbol_under_global.clone(), false);
        assert!(SymbolTable::is_symbol_under(0, &symbol_under_global));

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(2, SymbolTable::num_scopes());

        let symbol_under_child_of_global = Symbol::String(StringDecl::new(
            "child_of_global_symbol".to_owned(),
            "value1".to_owned(),
        ));

        // Should be added under "ChildOfGlobal" scope
        SymbolTable::add_symbol(symbol_under_child_of_global.clone(), false);
        assert!(SymbolTable::is_symbol_under(
            1,
            &symbol_under_child_of_global
        ));
    }

    #[test]
    #[serial]
    fn symbol_type_works() {
        setup();

        let symbol_under_global = Symbol::String(StringDecl::new(
            "global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol_under_global, false);
        assert_eq!(
            SymbolType::String,
            SymbolTable::symbol_type_for("global_symbol").unwrap()
        );
        assert!(SymbolTable::symbol_type_for("non_existent").is_none());

        SymbolTable::add_function_scope("ChildOfGlobal");
        let symbol_under_child_of_global = Symbol::String(StringDecl::new(
            "child_of_global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol_under_child_of_global, false);
        assert_eq!(
            SymbolType::String,
            SymbolTable::symbol_type_for("child_of_global_symbol").unwrap()
        );
        assert!(SymbolTable::symbol_type_for("non_existent").is_none());
    }

    #[test]
    #[serial]
    #[should_panic]
    fn symbol_table_access_after_sealing_results_in_panic() {
        setup();
        let symbol = Symbol::String(StringDecl::new(
            "global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol, false);
        assert!(SymbolTable::symbol_type_for("global_symbol").is_some());

        SymbolTable::seal();
        SymbolTable::symbol_type_for("global_symbol");
    }

    #[test]
    #[serial]
    fn adding_conflicting_symbols_in_same_scope_results_in_decl_error() {
        setup();
        let symbol = Symbol::String(StringDecl::new(
            "global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol.clone(), false);
        assert!(SymbolTable::add_symbol(symbol, false).err().is_some());
    }

    #[test]
    #[serial]
    fn symbol_table_to_list_of_symbols() {
        setup();

        let symbol_under_global = Symbol::String(StringDecl::new(
            "global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol_under_global.clone(), false);

        let symbol_under_anonymous_scope = Symbol::String(StringDecl::new(
            "anonymous_scope_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_anonymous_scope();
        SymbolTable::add_symbol(symbol_under_anonymous_scope.clone(), false);

        let symbol_under_child_of_global = Symbol::String(StringDecl::new(
            "child_of_global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_function_scope("ChildOfGlobal");
        SymbolTable::add_symbol(symbol_under_child_of_global.clone(), false);

        let symbols = SymbolTable::seal();
        assert_eq!(3, symbols.len());
        assert_eq!(symbol_under_global, symbols[0]);
        assert_eq!(symbol_under_anonymous_scope, symbols[1]);
        assert_eq!(symbol_under_child_of_global, symbols[2]);
    }
}
