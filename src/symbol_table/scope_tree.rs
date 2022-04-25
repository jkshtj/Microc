use crate::symbol_table::scope::Scope;
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

/// A tree like structure for representing
/// scopes. Each scope uses one table of
/// symbols per scope.
#[derive(Debug)]
pub struct ScopeTree {
    scopes: Vec<Rc<RefCell<Scope>>>,
    active_scope_stack: Vec<Rc<RefCell<Scope>>>,
}

impl Display for ScopeTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.scopes
            .iter()
            .try_for_each(|scope| writeln!(f, "{}", scope.borrow()))?;
        Ok(())
    }
}

impl ScopeTree {
    pub(crate) fn new() -> Self {
        let global = Rc::new(RefCell::new(Scope::new_global()));
        Self {
            scopes: vec![global.clone()],
            active_scope_stack: vec![global],
        }
    }

    pub(crate) fn global_scope(&self) -> Rc<RefCell<Scope>> {
        // Indexing is safe as we never initialize a
        // ScopeTree without a global scope.
        Rc::clone(&self.scopes[0])
    }

    pub(crate) fn active_scope(&self) -> Rc<RefCell<Scope>> {
        // Indexing is safe as we always have at least
        // the global scope in the ScopeTree.
        Rc::clone(&self.active_scope_stack[self.active_scope_stack.len() - 1])
    }

    pub(crate) fn add_new_scope(&mut self, scope: Scope) {
        let scope = Rc::new(RefCell::new(scope));
        self.scopes.push(Rc::clone(&scope));
        self.active_scope_stack.push(scope);
    }

    pub(crate) fn end_curr_scope(&mut self) {
        self.active_scope_stack.pop();
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.scopes.len()
    }
}

#[cfg(test)]
mod test {
    // TODO [unit tests]: Add unit tests
}
