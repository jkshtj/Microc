#![allow(unused)]

use crate::symbol_table::symbol::data::{DataSymbol, DataType};
use crate::symbol_table::symbol::function::FunctionSymbol;
use crate::symbol_table::symbol::NumType;
use atomic_refcell::AtomicRefCell;
use getset::Getters;
use linked_hash_set::LinkedHashSet;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};

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
    pub fn seal() -> Vec<DataSymbol> {
        let mut symbol_table = SYMBOL_TABLE.borrow_mut();
        if let SymbolTable::Active(ref mut scope_tree) = *symbol_table {
            let scopes = std::mem::take(&mut scope_tree.scopes);
            *symbol_table = SymbolTable::Sealed;
            scopes
                .into_iter()
                .flat_map(|scope| scope.into_data_symbols())
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
            scope_tree.add_new_scope(new_scope);

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
            scope_tree.add_new_scope(new_scope);

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

    pub fn add_data_symbol(
        symbol: DataSymbol,
        is_func_param: bool,
    ) -> Result<(), DeclarationError> {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            let active_scope = scope_tree.active_scope_mut();
            active_scope.add_data_symbol(symbol, is_func_param)?;
        } else {
            panic!("Symbol table has been sealed.");
        }

        Ok(())
    }

    pub fn add_function_symbol(symbol: FunctionSymbol) -> Result<(), DeclarationError> {
        if let SymbolTable::Active(ref mut scope_tree) = *SYMBOL_TABLE.borrow_mut() {
            let active_scope = scope_tree.active_scope_mut();
            active_scope.add_function_symbol(symbol)?;
        } else {
            panic!("Symbol table has been sealed.");
        }

        Ok(())
    }

    // TODO: Should this return a `Result`?
    pub fn symbol_type_for(symbol_name: &str) -> Option<DataType> {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let global_scope = scope_tree.global_scope();

            global_scope.data_symbol_type(symbol_name).or_else(|| {
                let active_scope = scope_tree.active_scope();
                active_scope.data_symbol_type(symbol_name)
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
    fn is_symbol_under(scope_id: usize, symbol: &DataSymbol) -> bool {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let scope = scope_tree.scopes.get(scope_id).unwrap();
            scope.data_symbols().contains(symbol)
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

    #[cfg(test)]
    fn active_scope_name() -> String {
        if let SymbolTable::Active(ref scope_tree) = *SYMBOL_TABLE.borrow() {
            let active_scope_id = *scope_tree.active_scope_stack.last().unwrap();
            let curr_scope = scope_tree.scopes.get(active_scope_id).unwrap();
            curr_scope.name().to_owned()
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
        // Indexing is safe as we never initialize a
        // ScopeTree without a global scope.
        &self.scopes[0]
    }

    fn global_scope_mut(&mut self) -> &mut Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without a global scope.
        &mut self.scopes[0]
    }

    fn active_scope(&self) -> &Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without an active scope.
        let active_scope_id = self.active_scope_stack[self.active_scope_stack.len() - 1];

        // Indexing is safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        &self.scopes[active_scope_id]
    }

    fn active_scope_mut(&mut self) -> &mut Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without an active scope.
        let active_scope_id = self.active_scope_stack[self.active_scope_stack.len() - 1];

        // Indexing is safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        &mut self.scopes[active_scope_id]
    }

    fn active_scope_id(&self) -> usize {
        // Indexing is safe as we never initialize a
        // ScopeTree without an active scope.
        self.active_scope_stack[self.active_scope_stack.len() - 1]
    }

    fn add_new_scope(&mut self, scope: Scope) {
        self.scopes.push(scope);
    }
}

#[derive(Debug)]
enum Scope {
    Global {
        data_symbols: LinkedHashSet<DataSymbol>,
        function_symbols: LinkedHashSet<FunctionSymbol>,
    },
    Anonymous {
        name: String,
        parent_id: Option<usize>,
        data_symbols: LinkedHashSet<DataSymbol>,
    },
    Function {
        name: String,
        parent_id: Option<usize>,
        data_symbols: LinkedHashSet<DataSymbol>,
        // Local variables have negative offsets
        // from the frame pointer and are therefore
        // signed integers.
        stack_frame_local_slot_map: HashMap<String, i32>,
        //  Global variables have positive offsets from
        // the frame pointer and are therefore unsigned
        // integers.
        stack_frame_param_slot_map: HashMap<String, u32>,
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
            }
            | Scope::Function {
                name, data_symbols, ..
            } => {
                writeln!(f, "Symbol table {}", self.name())?;
                data_symbols
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
            data_symbols: LinkedHashSet::new(),
            function_symbols: LinkedHashSet::new(),
        }
    }

    fn new_anonymous<T: ToString>(name: T, parent_id: Option<usize>) -> Self {
        Self::Anonymous {
            name: name.to_string(),
            parent_id,
            data_symbols: LinkedHashSet::new(),
        }
    }

    fn new_function<T: ToString>(name: T, parent_id: Option<usize>) -> Self {
        Self::Function {
            name: name.to_string(),
            parent_id,
            data_symbols: LinkedHashSet::new(),
            stack_frame_local_slot_map: HashMap::new(),
            stack_frame_param_slot_map: HashMap::new(),
        }
    }

    fn add_function_symbol(&mut self, symbol: FunctionSymbol) -> Result<(), DeclarationError> {
        if self.contains_function_symbol(&symbol) {
            return Err(DeclarationError::new(
                self.name().to_owned(),
                symbol.name().to_owned(),
            ));
        }

        match self {
            Scope::Global {
                function_symbols, ..
            } => function_symbols.insert(symbol),
            // TODO: Better error here.
            _ => panic!("Cannot add function symbol to a non-global scope!"),
        };

        Ok(())
    }

    fn add_data_symbol(
        &mut self,
        symbol: DataSymbol,
        is_func_param: bool,
    ) -> Result<(), DeclarationError> {
        if self.contains_data_symbol(&symbol) {
            return Err(DeclarationError::new(
                self.name().to_owned(),
                symbol.name().to_owned(),
            ));
        }

        match self {
            Scope::Global { data_symbols, .. } | Scope::Anonymous { data_symbols, .. } => {
                data_symbols.insert(symbol);
            }
            Scope::Function {
                data_symbols,
                stack_frame_local_slot_map,
                stack_frame_param_slot_map,
                ..
            } => {
                if is_func_param {
                    stack_frame_param_slot_map.insert(
                        symbol.name().to_owned(),
                        STACK_FRAME_PARAM_SLOT_COUNTER.fetch_add(1, Ordering::SeqCst),
                    );
                } else {
                    stack_frame_local_slot_map.insert(
                        symbol.name().to_owned(),
                        STACK_FRAME_LOCAL_SLOT_COUNTER.fetch_sub(1, Ordering::SeqCst),
                    );
                }
                data_symbols.insert(symbol);
            }
        };
        Ok(())
    }

    fn data_symbols(&self) -> &LinkedHashSet<DataSymbol> {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. }
            | Scope::Function { data_symbols, .. } => data_symbols,
        }
    }

    fn into_data_symbols(self) -> Vec<DataSymbol> {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. }
            | Scope::Function { data_symbols, .. } => data_symbols.into_iter().collect(),
        }
    }

    fn name(&self) -> &str {
        match self {
            Scope::Global { .. } => "GLOBAL",
            Scope::Anonymous { name, .. } | Scope::Function { name, .. } => name,
        }
    }

    fn contains_data_symbol(&self, symbol: &DataSymbol) -> bool {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. }
            | Scope::Function { data_symbols, .. } => data_symbols.contains(symbol),
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

    // TODO: Should this return a `Result`?
    fn data_symbol_type(&self, symbol_name: &str) -> Option<DataType> {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. }
            | Scope::Function { data_symbols, .. } => data_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| match symbol {
                    DataSymbol::String { .. } => DataType::String,
                    DataSymbol::Int { .. } => DataType::Num(NumType::Int),
                    DataSymbol::Float { .. } => DataType::Num(NumType::Float),
                }),
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

pub mod symbol {
    #[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
    pub enum NumType {
        Int,
        Float,
    }

    pub mod data {
        use crate::symbol_table::symbol::NumType;

        #[derive(Debug, Eq, PartialEq, Copy, Clone)]
        pub enum DataType {
            String,
            Num(NumType),
        }

        /// Represents a symbol declared in
        /// the program to represent data -
        /// string, int or a float.
        #[derive(Debug, PartialEq, Clone, Hash, Eq, derive_more::Display)]
        pub enum DataSymbol {
            #[display(fmt = "name {} type STRING value {}\n", name, value)]
            String { name: String, value: String },
            #[display(fmt = "name {} type INT\n", name)]
            Int { name: String },
            #[display(fmt = "name {} type FLOAT\n", name)]
            Float { name: String },
        }

        impl DataSymbol {
            pub fn name(&self) -> &str {
                match self {
                    DataSymbol::String { name, value } => name,
                    DataSymbol::Int { name } => name,
                    DataSymbol::Float { name } => name,
                }
            }
        }
    }

    pub mod function {
        use crate::symbol_table::symbol::NumType;

        /// Represents possible return types
        /// in a function.
        #[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
        pub enum ReturnType {
            Num(NumType),
            Void,
        }

        /// Represents function or non-data
        /// symbols in the program.
        #[derive(Debug, PartialEq, Clone, Hash, Eq)]
        pub struct FunctionSymbol {
            name: String,
            return_type: ReturnType,
            param_list: Vec<NumType>,
        }

        impl FunctionSymbol {
            pub fn name(&self) -> &str {
                &self.name
            }
        }
    }
}

// TODO: Add tests for function symbols
#[cfg(test)]
mod test {
    // Symbol table does not support
    // concurrent modification.
    use super::*;
    use crate::symbol_table::symbol::data::DataType;
    use crate::token::{Token, TokenType};
    use serial_test::serial;

    fn setup() {
        let mut symbol_table = SYMBOL_TABLE.borrow_mut();
        if let SymbolTable::Active(ref mut scope_tree) = *symbol_table {
            *scope_tree = ScopeTree::new();
            ANONYMOUS_SCOPE_COUNTER.store(1, Ordering::SeqCst);
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

        let symbol_under_global = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };

        // Should be added under "GLOBAL" scope
        SymbolTable::add_data_symbol(symbol_under_global.clone(), false);
        assert!(SymbolTable::is_symbol_under(0, &symbol_under_global));

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(2, SymbolTable::num_scopes());

        let symbol_under_child_of_global = DataSymbol::String {
            name: "child_of_global_symbol".to_owned(),
            value: "value1".to_owned(),
        };

        // Should be added under "ChildOfGlobal" scope
        SymbolTable::add_data_symbol(symbol_under_child_of_global.clone(), false);
        assert!(SymbolTable::is_symbol_under(
            1,
            &symbol_under_child_of_global
        ));
    }

    #[test]
    #[serial]
    fn symbol_type_works() {
        setup();

        let symbol_under_global = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_data_symbol(symbol_under_global, false);
        assert_eq!(
            DataType::String,
            SymbolTable::symbol_type_for("global_symbol").unwrap()
        );
        assert!(SymbolTable::symbol_type_for("non_existent").is_none());

        SymbolTable::add_function_scope("ChildOfGlobal");
        let symbol_under_child_of_global = DataSymbol::String {
            name: "child_of_global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_data_symbol(symbol_under_child_of_global, false);
        assert_eq!(
            DataType::String,
            SymbolTable::symbol_type_for("child_of_global_symbol").unwrap()
        );
        assert!(SymbolTable::symbol_type_for("non_existent").is_none());
    }

    #[test]
    #[serial]
    #[should_panic]
    fn symbol_table_access_after_sealing_results_in_panic() {
        setup();
        let symbol = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_data_symbol(symbol.clone(), false);
        SymbolTable::seal();
        SymbolTable::add_data_symbol(symbol, false);
    }

    #[test]
    #[serial]
    fn adding_conflicting_symbols_in_same_scope_results_in_decl_error() {
        setup();
        let symbol = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_data_symbol(symbol.clone(), false);
        assert!(SymbolTable::add_data_symbol(symbol, false).err().is_some());
    }

    #[test]
    #[serial]
    fn symbol_table_to_list_of_symbols() {
        setup();

        let symbol_under_global = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_data_symbol(symbol_under_global.clone(), false);

        let symbol_under_anonymous_scope = DataSymbol::String {
            name: "anonymous_scope_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_anonymous_scope();
        SymbolTable::add_data_symbol(symbol_under_anonymous_scope.clone(), false);

        let symbol_under_child_of_global = DataSymbol::String {
            name: "child_of_global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_function_scope("ChildOfGlobal");
        SymbolTable::add_data_symbol(symbol_under_child_of_global.clone(), false);

        let symbols = SymbolTable::seal();
        assert_eq!(3, symbols.len());
        assert_eq!(symbol_under_global, symbols[0]);
        assert_eq!(symbol_under_anonymous_scope, symbols[1]);
        assert_eq!(symbol_under_child_of_global, symbols[2]);
    }
}
