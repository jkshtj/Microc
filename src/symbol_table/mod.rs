#![allow(unused)]

pub mod decl;

use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};

use atomic_refcell::AtomicRefCell;
use getset::Getters;
use crate::symbol_table::decl::{StringDecl, IntDecl, FloatDecl};

lazy_static::lazy_static! {
    pub static ref SYMBOL_TABLE: AtomicRefCell<SymbolTable> = AtomicRefCell::new(SymbolTable::new());
}

#[derive(Debug, derive_more::Error, derive_more::Display, Getters)]
#[display(fmt = "Symbol [{}] was declared in scope [{}] multiple times.", symbol_name, scope_name)]
#[getset(get = "pub")]
pub struct DeclarationError {
    scope_name: String,
    symbol_name: String,
}

impl DeclarationError {
    pub fn new(scope_name: String, symbol_name: String) -> Self {
        DeclarationError { scope_name, symbol_name }
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    scope_tree: Vec<Scope>,
    active_scope_stack: Vec<usize>,
    anonymous_scope_counter: u32,
    decl_error: Option<DeclarationError>,
}

impl Display for SymbolTable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(decl_err) = &self.decl_error {
            writeln!(f, "DECLARATION ERROR {}", decl_err.symbol_name())?
        } else {
            self.scope_tree.iter().try_for_each(|scope| {
                writeln!(f, "{}", scope)
            })?;
        }
        Ok(())
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            scope_tree: vec![
                Scope::new("GLOBAL", None)
            ],
            active_scope_stack: vec![0],
            anonymous_scope_counter: 0,
            decl_error: None,
        }
    }

    pub fn set_decl_error(decl_error: DeclarationError) {
        if let Ok(mut symbol_table) = SYMBOL_TABLE.try_borrow_mut() {
            symbol_table.decl_error.replace(decl_error);
        } else {
            todo!("Log a message/error!")
        }
    }

    pub fn add_anonymous_scope() {
        if let Ok(mut symbol_table) = SYMBOL_TABLE.try_borrow_mut() {
            let active_scope_id = symbol_table.active_scope_id();

            symbol_table.anonymous_scope_counter += 1;
            let anonymous_scope_name = format!("BLOCK{}", symbol_table.anonymous_scope_counter);
            let new_scope = Scope::new(anonymous_scope_name, Some(active_scope_id));
            symbol_table.scope_tree.push(new_scope);

            let new_scope_id = symbol_table.scope_tree.len() - 1;
            symbol_table.active_scope_stack.push(new_scope_id);
        } else {
            todo!("Log a message/error!")
        }
    }

    pub fn add_scope<T: ToString + Debug>(name: T) {
        if let Ok(mut symbol_table) = SYMBOL_TABLE.try_borrow_mut() {
            let active_scope_id = symbol_table.active_scope_id();

            let new_scope = Scope::new(name, Some(active_scope_id));
            symbol_table.scope_tree.push(new_scope);

            let new_scope_id = symbol_table.scope_tree.len() - 1;
            symbol_table.active_scope_stack.push(new_scope_id);
        } else {
            todo!("Log a message/error!")
        }
    }

    pub fn end_curr_scope() {
        if let Ok(mut symbol_table) = SYMBOL_TABLE.try_borrow_mut() {
            symbol_table.active_scope_stack.pop();
        } else {
            todo!("Log a message/error")
        }
    }

    pub fn add_symbol<T: Into<Symbol> + Debug>(symbol: T) -> Result<(), DeclarationError> {
        if let Ok(mut symbol_table) = SYMBOL_TABLE.try_borrow_mut() {
            let active_scope = symbol_table.active_scope_mut();
            active_scope.add_symbol(symbol.into())?;
        } else {
            todo!("Log a message/error")
        }

        Ok(())
    }

    // TODO: Should this return a `Result`?
    pub fn symbol_type_for(symbol_name: &str) -> Option<SymbolType> {
        if let Ok(symbol_table) = SYMBOL_TABLE.try_borrow() {
            let global_scope = symbol_table.global_scope();

            global_scope.symbol_type(symbol_name).or_else(|| {
                let active_scope = symbol_table.active_scope();
                active_scope.symbol_type(symbol_name)
            })
        } else {
            todo!("Log a message/error")
        }
    }

    fn global_scope(&self) -> &Scope {
        // Unwrapping here should be safe as we never initialize a
        // symbol table without a global scope.
        self.scope_tree.first().unwrap()
    }

    fn global_scope_mut(&mut self) -> &mut Scope {
        // Unwrapping here should be safe as we never initialize a
        // symbol table without a global scope.
        self.scope_tree.first_mut().unwrap()
    }

    fn active_scope(&self) -> &Scope {
        // Unwrapping here should be safe as we never create a
        // SymbolTable without setting an active scope.
        let active_scope_id = *self.active_scope_stack.last().unwrap();

        // Unwrapping here should be safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        self.scope_tree.get(active_scope_id).unwrap()
    }

    fn active_scope_mut(&mut self) -> &mut Scope {
        // Unwrapping here should be safe as we never create a
        // SymbolTable without setting an active scope.
        let active_scope_id = *self.active_scope_stack.last().unwrap();

        // Unwrapping here should be safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        self.scope_tree.get_mut(active_scope_id).unwrap()
    }

    fn active_scope_id(&self) -> usize {
        // Unwrapping here should be safe as we never create a
        // SymbolTable without setting an active scope.
        *self.active_scope_stack.last().unwrap()
    }

    #[cfg(test)]
    fn print_symbol_table() {
        if let Ok(symbol_table) = SYMBOL_TABLE.try_borrow() {
            println!("{}", &*symbol_table);
        } else {
            todo!("Log a message/error")
        }
    }

    #[cfg(test)]
    fn num_scopes() -> usize {
        SYMBOL_TABLE.borrow().scope_tree.len()
    }

    #[cfg(test)]
    fn curr_scope() -> usize {
        *SYMBOL_TABLE.borrow().active_scope_stack.last().unwrap()
    }

    #[cfg(test)]
    fn parent_of_scope(id: usize) -> Option<usize> {
        let symbol_table =  SYMBOL_TABLE.borrow();
        let scope = symbol_table.scope_tree.get(id).unwrap();
        scope.parent_id
    }

    #[cfg(test)]
    fn is_symbol_under(scope_id: usize, symbol: &Symbol) -> bool {
        let symbol_table =  SYMBOL_TABLE.borrow();
        let scope = symbol_table.scope_tree.get(scope_id).unwrap();
        scope.symbols.contains(symbol)
    }

    #[cfg(test)]
    fn is_active_scope_name(name: &'static str) -> bool {
        let symbol_tree = SYMBOL_TABLE.borrow();
        let active_scope_id = *symbol_tree.active_scope_stack.last().unwrap();
        let curr_scope = symbol_tree.scope_tree.get(active_scope_id).unwrap();
        &curr_scope.name == name
    }
}

#[derive(Debug)]
struct Scope {
    name: String,
    parent_id: Option<usize>,
    symbols: Vec<Symbol>,
    symbol_set: HashSet<String>,
}

impl Display for Scope {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Symbol table {}", self.name)?;
        self.symbols.iter().try_for_each(|symbol| {
            writeln!(f, "{}", symbol)
        })?;
        Ok(())
    }
}

impl Scope {
    fn new<T: ToString>(
        name: T,
        parent_id: Option<usize>,
    ) -> Self {
        Self {
            name: name.to_string(),
            parent_id,
            symbols: vec![],
            symbol_set: HashSet::new(),
        }
    }

    fn add_symbol(&mut self, symbol: Symbol) -> Result<(), DeclarationError> {
        let symbol_name = symbol.get_name();
        if self.contains_symbol(symbol_name) {
            return Err(DeclarationError::new(self.name.clone(), symbol_name.to_string()));
        }
        self.symbol_set.insert(symbol_name.to_owned());
        self.symbols.push(symbol);
        Ok(())
    }

    // TODO: Should this return a `Result`?
    // TODO: Do we need to store symbols in a Vec?
    //  Or was it just a requirement in stage3?
    fn symbol_type(&self, symbol_name: &str) -> Option<SymbolType> {
        self.symbols
            .iter()
            .find(|&symbol| symbol.get_name() == symbol_name)
            .map(|symbol| match symbol {
                Symbol::String(_) => SymbolType::String,
                Symbol::Int(_) => SymbolType::Num(NumType::Int),
                Symbol::Float(_) => SymbolType::Num(NumType::Float),
            })
    }

    fn contains_symbol(&self, symbol_name: &str) -> bool {
        self.symbol_set.contains(symbol_name)
    }
}

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

#[derive(Debug, Eq, PartialEq)]
pub enum SymbolType {
    String,
    Num(NumType),
}

#[derive(Debug, Eq, PartialEq)]
pub enum NumType {
    Int,
    Float
}

#[cfg(test)]
mod test {
    use crate::token::{Token, TokenType};
    // Need serial tests because different tests
    // modify the same symbol table.
    use serial_test::serial;
    use super::*;

    fn setup() {
        let mut symbol_table = SYMBOL_TABLE.borrow_mut();
        *symbol_table = SymbolTable::new();
    }

    #[test]
    #[serial]
    fn first_access_to_symbol_table_works() {
        setup();
        let symbol_table = SYMBOL_TABLE.borrow();
        println!("{:?}", symbol_table);
    }

    #[test]
    #[serial]
    fn add_scope_works() {
        setup();

        SymbolTable::add_scope("ChildOfGlobal");
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

        SymbolTable::add_scope("ChildOfGlobal");
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
        SymbolTable::add_symbol(symbol_under_global.clone());
        assert!(SymbolTable::is_symbol_under(0, &symbol_under_global));

        SymbolTable::add_scope("ChildOfGlobal");
        assert_eq!(2, SymbolTable::num_scopes());

        let symbol_under_child_of_global = Symbol::String(StringDecl::new(
            "child_of_global_symbol".to_owned(),
            "value1".to_owned(),
        ));

        // Should be added under "ChildOfGlobal" scope
        SymbolTable::add_symbol(symbol_under_child_of_global.clone());
        assert!(SymbolTable::is_symbol_under(1, &symbol_under_child_of_global));
    }

    #[test]
    #[serial]
    fn symbol_type_works() {
        setup();

        let symbol_under_global = Symbol::String(StringDecl::new(
            "global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol_under_global.clone());
        assert_eq!(SymbolType::String, SymbolTable::symbol_type_for("global_symbol").unwrap());
        assert!(SymbolTable::symbol_type_for("non_existent").is_none());

        SymbolTable::add_scope("ChildOfGlobal");
        let symbol_under_child_of_global = Symbol::String(StringDecl::new(
            "child_of_global_symbol".to_owned(),
            "value1".to_owned(),
        ));
        SymbolTable::add_symbol(symbol_under_child_of_global.clone());
        assert_eq!(SymbolType::String, SymbolTable::symbol_type_for("child_of_global_symbol").unwrap());
        assert!(SymbolTable::symbol_type_for("non_existent").is_none());
    }

    // TODO: Add test for testing symbol conflict in scope
}
