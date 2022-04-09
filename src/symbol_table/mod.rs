#![allow(unused)]

pub mod error;
pub mod scope;
pub mod scope_tree;
pub mod symbol;

use crate::symbol_table::error::{
    DeclareExistingSymbolError, SymbolError, UseUndeclaredSymbolError,
};
use crate::symbol_table::scope::Scope;
use crate::symbol_table::scope_tree::ScopeTree;
use crate::symbol_table::symbol::data;
use crate::symbol_table::symbol::function;
use crate::symbol_table::symbol::NumType;
use linked_hash_set::LinkedHashSet;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};

thread_local! {
    /// Thread local, global symbol table that
    /// assumes the compiler to be single threaded.
    pub static SYMBOL_TABLE: RefCell<SymbolTable> = RefCell::new(SymbolTable {
        scope_tree: ScopeTree::new(),
        symbol_errors: vec![],
    });
}

static ANONYMOUS_SCOPE_COUNTER: AtomicU32 = AtomicU32::new(1);

/// Global symbol table that consists
/// of a scope tree, which further consists
/// of multiple scopes each with its own
/// symbol table.
#[derive(Debug)]
pub struct SymbolTable {
    scope_tree: ScopeTree,
    symbol_errors: Vec<SymbolError>,
}

impl SymbolTable {
    pub fn add_symbol_error(error: SymbolError) {
        SYMBOL_TABLE.with(|symbol_table| {
            symbol_table.borrow_mut().symbol_errors.push(error);
        })
    }

    pub fn add_anonymous_scope() {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope();

            let anonymous_scope_name = format!(
                "BLOCK{}",
                ANONYMOUS_SCOPE_COUNTER.fetch_add(1, Ordering::SeqCst)
            );
            let new_scope = Scope::new_anonymous(anonymous_scope_name, active_scope);
            scope_tree.add_new_scope(new_scope);
        })
    }

    pub fn add_function_scope<T: ToString + Debug>(name: T) {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope();

            let new_scope = Scope::new_function(name, active_scope);
            scope_tree.add_new_scope(new_scope);
        })
    }

    pub fn end_curr_scope() {
        SYMBOL_TABLE.with(|symbol_table| {
            symbol_table.borrow_mut().scope_tree.end_curr_scope();
        })
    }

    // TODO: add relevant unit tests
    pub fn add_non_func_scoped_symbol(symbol: data::NonFunctionScopedSymbol) -> Result<(), SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope();
            active_scope.borrow_mut().add_non_func_scoped_symbol(symbol)?;
            Ok(())
        })
    }

    // TODO: add relevant unit tests
    pub fn add_func_scoped_symbol(name: String, symbol: data::FunctionScopedSymbol) -> Result<(), SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope();
            active_scope.borrow_mut().add_func_scoped_symbol(name, symbol)?;
            Ok(())
        })
    }

    // TODO: add relevant unit tests
    pub fn add_function_symbol(symbol: function::Symbol) -> Result<(), SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            // Functions can only be declared in global scope
            scope_tree.global_scope().borrow_mut().add_function_symbol(symbol)?;
            Ok(())
        })
    }

    // TODO: add relevant unit tests
    pub fn data_symbol_for_name(symbol_name: &str) -> Result<data::Symbol, SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            Ok(scope_tree.active_scope().borrow().data_symbol_for_name(symbol_name)?)
        })
    }

    // TODO: add relevant unit tests
    pub fn function_symbol_for_name(symbol_name: &str) -> Result<Rc<function::Symbol>, SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            // Functions are only declared in global scope and
            // therefore it makes sense to only look for them
            // in the global scope.
            Ok(scope_tree.global_scope().borrow().function_symbol_for_name(symbol_name)?)
        })
    }

    #[cfg(test)]
    fn print_symbol_table() {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            println!("{}", scope_tree);
        })
    }

    #[cfg(test)]
    fn num_scopes() -> usize {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            scope_tree.len()
        })
    }

    #[cfg(test)]
    fn global_scope() -> Rc<RefCell<Scope>> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            scope_tree.global_scope()
        })
    }

    #[cfg(test)]
    fn active_scope() -> Rc<RefCell<Scope>> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            scope_tree.active_scope()
        })
    }

    #[cfg(test)]
    fn is_data_symbol_under(scope: Rc<RefCell<Scope>>, symbol_name: &str) -> bool {
        scope
            .borrow()
            .data_symbol_for_name(symbol_name)
            .map_or(false, |_| true)
    }

    #[cfg(test)]
    fn parent_of_scope(scope: &Rc<RefCell<Scope>>) -> Rc<RefCell<Scope>> {
        scope.borrow().parent()
    }

    #[cfg(test)]
    fn is_active_scope_name(name: &'static str) -> bool {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            let active_scope = scope_tree.active_scope();
            let active_scope = active_scope.borrow();
            active_scope.name() == name
        })
    }

    #[cfg(test)]
    fn active_scope_name() -> String {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            let active_scope = scope_tree.active_scope();
            let active_scope = active_scope.borrow();
            active_scope.name().to_owned()
        })
    }
}

#[cfg(test)]
mod test {
    // Symbol table does not support
    // concurrent modification.
    use super::*;
    use crate::symbol_table::scope_tree::ScopeTree;
    use crate::symbol_table::symbol::data::DataType;
    use crate::token::{Token, TokenType};
    use serial_test::serial;

    fn setup() {
        SYMBOL_TABLE.with(|symbol_table| {
            let mut symbol_table = symbol_table.borrow_mut();

            *symbol_table = SymbolTable {
                scope_tree: ScopeTree::new(),
                symbol_errors: vec![],
            };

            ANONYMOUS_SCOPE_COUNTER.store(1, Ordering::SeqCst);
        })
    }

    #[test]
    #[serial]
    fn add_scope_works() {
        setup();

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(2, SymbolTable::num_scopes());

        let curr_scope = SymbolTable::active_scope();
        let global_scope = SymbolTable::global_scope();
        assert_eq!(global_scope, SymbolTable::parent_of_scope(&curr_scope));
    }

    #[test]
    #[serial]
    fn add_anonymous_scope_works() {
        setup();
        assert!(SymbolTable::is_active_scope_name("GLOBAL"));

        let global_scope = SymbolTable::global_scope();

        SymbolTable::add_anonymous_scope();
        // Num scopes
        assert_eq!(2, SymbolTable::num_scopes());
        // Anonymous scope names
        assert!(SymbolTable::is_active_scope_name("BLOCK1"));
        let curr_scope1 = SymbolTable::active_scope();
        // Scope parents
        assert_eq!(global_scope, SymbolTable::parent_of_scope(&curr_scope1));

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(3, SymbolTable::num_scopes());
        assert!(SymbolTable::is_active_scope_name("ChildOfGlobal"));
        let curr_scope2 = SymbolTable::active_scope();
        assert_eq!(curr_scope1, SymbolTable::parent_of_scope(&curr_scope2));

        SymbolTable::add_anonymous_scope();
        // Num scopes
        assert_eq!(4, SymbolTable::num_scopes());
        // Anonymous scope names
        assert!(SymbolTable::is_active_scope_name("BLOCK2"));
        let curr_scope3 = SymbolTable::active_scope();
        // Scope parents
        assert_eq!(curr_scope2, SymbolTable::parent_of_scope(&curr_scope3));
    }

    #[test]
    #[serial]
    // TODO: Test needs to be updated to reflect changes in
    // FunctionScope and take into account the addition of
    // the FunctionDataSymbol type
    fn add_symbol_works() {
        setup();

        let symbol_under_global = data::NonFunctionScopedSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };

        let global = SymbolTable::global_scope();
        // Should be added under "GLOBAL" scope
        SymbolTable::add_non_func_scoped_symbol(symbol_under_global.clone());
        assert!(SymbolTable::is_data_symbol_under(
            global,
            symbol_under_global.name()
        ));

        SymbolTable::add_anonymous_scope();
        assert_eq!(2, SymbolTable::num_scopes());

        let symbol_under_child_of_global = data::NonFunctionScopedSymbol::String {
            name: "child_of_global_symbol".to_owned(),
            value: "value1".to_owned(),
        };

        let child_of_global = SymbolTable::active_scope();
        // Should be added under "ChildOfGlobal" scope
        SymbolTable::add_non_func_scoped_symbol(symbol_under_child_of_global.clone());
        assert!(SymbolTable::is_data_symbol_under(
            child_of_global,
            symbol_under_child_of_global.name()
        ));
    }

    #[test]
    #[serial]
    fn adding_conflicting_symbols_in_same_scope_results_in_symbol_error() {
        setup();
        let symbol = data::NonFunctionScopedSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_non_func_scoped_symbol(symbol.clone());
        assert!(SymbolTable::add_non_func_scoped_symbol(symbol).err().is_some());
    }
}
