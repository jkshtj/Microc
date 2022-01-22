use std::fmt::{Display, Formatter};
use crate::symbol_table::scope::Scope;

/// A tree like structure for representing
/// scopes. Each scope uses one table of
/// symbols per scope.
#[derive(Debug)]
pub struct ScopeTree {
    scopes: Vec<Scope>,
    active_scope_stack: Vec<usize>,
}

impl Display for ScopeTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.scopes
            .iter()
            .try_for_each(|scope| writeln!(f, "{}", scope))?;
        Ok(())
    }
}

impl ScopeTree {
    pub(crate) fn new() -> Self {
        Self {
            scopes: vec![Scope::new_global()],
            active_scope_stack: vec![0],
        }
    }

    pub(crate) fn global_scope(&self) -> &Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without a global scope.
        &self.scopes[0]
    }

    pub(crate) fn global_scope_mut(&mut self) -> &mut Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without a global scope.
        &mut self.scopes[0]
    }

    pub(crate) fn active_scope(&self) -> &Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without an active scope.
        let active_scope_id = self.active_scope_stack[self.active_scope_stack.len() - 1];

        // Indexing is safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        &self.scopes[active_scope_id]
    }

    pub(crate) fn active_scope_mut(&mut self) -> &mut Scope {
        // Indexing is safe as we never initialize a
        // ScopeTree without an active scope.
        let active_scope_id = self.active_scope_stack[self.active_scope_stack.len() - 1];

        // Indexing is safe as we always insert a
        // scope into the scope tree before inserting its id
        // into the active scope stack.
        &mut self.scopes[active_scope_id]
    }

    pub(crate) fn active_scope_id(&self) -> usize {
        // Indexing is safe as we never initialize a
        // ScopeTree without an active scope.
        self.active_scope_stack[self.active_scope_stack.len() - 1]
    }

    pub(crate) fn add_new_scope(&mut self, scope: Scope) {
        self.scopes.push(scope);
        let new_scope_id = self.scopes.len() - 1;
        self.active_scope_stack.push(new_scope_id);
    }

    pub(crate) fn end_curr_scope(&mut self) {
        self.active_scope_stack.pop();
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.scopes.len()
    }

    #[cfg(test)]
    pub(crate) fn scope(&self, id: usize) -> &Scope {
        self.scopes.get(id).unwrap()
    }

    #[cfg(test)]
    pub(crate) fn parent_id(&self, scope_id: usize) -> Option<usize> {
        let scope = self.scopes.get(scope_id).unwrap();
        scope.parent_id()
    }
}

#[cfg(test)]
mod test {
    // TODO: Add unit tests
}