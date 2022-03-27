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
use crate::symbol_table::symbol::data::{DataSymbol, DataType, FunctionDataSymbol};
use crate::symbol_table::symbol::function::FunctionSymbol;
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
            let active_scope_id = scope_tree.active_scope_id();

            let anonymous_scope_name = format!(
                "BLOCK{}",
                ANONYMOUS_SCOPE_COUNTER.fetch_add(1, Ordering::SeqCst)
            );
            let new_scope = Scope::new_anonymous(anonymous_scope_name, Some(active_scope_id));
            scope_tree.add_new_scope(new_scope);
        })
    }

    pub fn add_function_scope<T: ToString + Debug>(name: T) {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope_id = scope_tree.active_scope_id();

            let new_scope = Scope::new_function(name, Some(active_scope_id));
            scope_tree.add_new_scope(new_scope);
        })
    }

    pub fn end_curr_scope() {
        SYMBOL_TABLE.with(|symbol_table| {
            symbol_table.borrow_mut().scope_tree.end_curr_scope();
        })
    }

    // TODO: add relevant unit tests
    pub fn add_data_symbol(symbol: DataSymbol) -> Result<(), SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope_mut();
            active_scope.add_data_symbol(symbol)?;
            Ok(())
        })
    }

    // TODO: add relevant unit tests
    pub fn add_func_data_symbol(name: String, symbol: FunctionDataSymbol) -> Result<(), SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope_mut();
            active_scope.add_func_data_symbol(name, symbol)?;
            Ok(())
        })
    }

    // TODO: add relevant unit tests
    pub fn add_function_symbol(symbol: FunctionSymbol) -> Result<(), SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &mut symbol_table.borrow_mut().scope_tree;
            let active_scope = scope_tree.active_scope_mut();
            active_scope.add_function_symbol(symbol)?;
            Ok(())
        })
    }

    // TODO: add relevant unit tests
    pub fn data_symbol_for_name(symbol_name: &str) -> Result<Rc<DataSymbol>, SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            Ok(scope_tree.active_scope().data_symbol_for_name(symbol_name)?)
        })
    }

    // TODO: add relevant unit tests
    pub fn function_symbol_for_name(symbol_name: &str) -> Result<Rc<FunctionSymbol>, SymbolError> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            Ok(scope_tree.active_scope().function_symbol_for_name(symbol_name)?)
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
    fn active_scope_id() -> usize {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            scope_tree.active_scope_id()
        })
    }

    #[cfg(test)]
    fn parent_of_scope(id: usize) -> Option<usize> {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            scope_tree.parent_id(id)
        })
    }

    #[cfg(test)]
    fn is_data_symbol_under(scope_id: usize, symbol_name: &str) -> bool {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            let scope = scope_tree.scope(scope_id);
            scope
                .data_symbol_for_name(symbol_name)
                .map_or(false, |_| true)
        })
    }

    #[cfg(test)]
    fn is_active_scope_name(name: &'static str) -> bool {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            let active_scope_id = scope_tree.active_scope_id();
            let curr_scope = scope_tree.scope(active_scope_id);
            curr_scope.name() == name
        })
    }

    #[cfg(test)]
    fn active_scope_name() -> String {
        SYMBOL_TABLE.with(|symbol_table| {
            let scope_tree = &symbol_table.borrow().scope_tree;
            let active_scope_id = scope_tree.active_scope_id();
            let curr_scope = scope_tree.scope(active_scope_id);
            curr_scope.name().to_owned()
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

        let curr_scope = SymbolTable::active_scope_id();
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
        let curr_scope = SymbolTable::active_scope_id();
        // Scope parents
        assert_eq!(Some(0), SymbolTable::parent_of_scope(curr_scope));

        SymbolTable::add_function_scope("ChildOfGlobal");
        assert_eq!(3, SymbolTable::num_scopes());
        assert!(SymbolTable::is_active_scope_name("ChildOfGlobal"));
        let curr_scope = SymbolTable::active_scope_id();
        assert_eq!(Some(1), SymbolTable::parent_of_scope(curr_scope));

        SymbolTable::add_anonymous_scope();
        // Num scopes
        assert_eq!(4, SymbolTable::num_scopes());
        // Anonymous scope names
        assert!(SymbolTable::is_active_scope_name("BLOCK2"));
        let curr_scope = SymbolTable::active_scope_id();
        // Scope parents
        assert_eq!(Some(2), SymbolTable::parent_of_scope(curr_scope));
    }

    #[test]
    #[serial]
    // TODO: Test needs to be updated to reflect changes in
    // FunctionScope and take into account the addition of
    // the FunctionDataSymbol type
    fn add_symbol_works() {
        setup();

        let symbol_under_global = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };

        // Should be added under "GLOBAL" scope
        SymbolTable::add_data_symbol(symbol_under_global.clone());
        assert!(SymbolTable::is_data_symbol_under(
            0,
            symbol_under_global.name()
        ));

        SymbolTable::add_anonymous_scope();
        assert_eq!(2, SymbolTable::num_scopes());

        let symbol_under_child_of_global = DataSymbol::String {
            name: "child_of_global_symbol".to_owned(),
            value: "value1".to_owned(),
        };

        // Should be added under "ChildOfGlobal" scope
        SymbolTable::add_data_symbol(symbol_under_child_of_global.clone());
        assert!(SymbolTable::is_data_symbol_under(
            1,
            symbol_under_child_of_global.name()
        ));
    }

    #[test]
    #[serial]
    fn adding_conflicting_symbols_in_same_scope_results_in_symbol_error() {
        setup();
        let symbol = DataSymbol::String {
            name: "global_symbol".to_owned(),
            value: "value1".to_owned(),
        };
        SymbolTable::add_data_symbol(symbol.clone());
        assert!(SymbolTable::add_data_symbol(symbol).err().is_some());
    }
}
