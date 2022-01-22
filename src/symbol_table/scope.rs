use linked_hash_set::LinkedHashSet;
use std::rc::Rc;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use crate::symbol_table::error::{DeclareExistingSymbolError, UseUndeclaredSymbolError};
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};
use crate::symbol_table::symbol::data::DataSymbol;
use crate::symbol_table::symbol::function::FunctionSymbol;

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
        data_symbols: LinkedHashSet<Rc<DataSymbol>>,
        // Local variables have negative offsets
        // from the frame pointer and are therefore
        // signed integers.
        stack_frame_local_slot_map: HashMap<Rc<DataSymbol>, i32>,
        //  Global variables have positive offsets from
        // the frame pointer and are therefore unsigned
        // integers.
        stack_frame_param_slot_map: HashMap<Rc<DataSymbol>, u32>,
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
            data_symbols: LinkedHashSet::new(),
            stack_frame_local_slot_map: HashMap::new(),
            stack_frame_param_slot_map: HashMap::new(),
        }
    }

    pub(crate) fn name(&self) -> &str {
        match self {
            Scope::Global { .. } => "GLOBAL",
            Scope::Anonymous { name, .. } | Scope::Function { name, .. } => name,
        }
    }

    pub(crate) fn add_function_symbol(&mut self, symbol: FunctionSymbol) -> Result<(), DeclareExistingSymbolError> {
        if self.contains_function_symbol(&symbol) {
            return Err(DeclareExistingSymbolError::new(
                self.name().to_owned(),
                symbol.name().to_owned(),
            ));
        }

        match self {
            Scope::Global {
                function_symbols, ..
            } => function_symbols.insert(Rc::new(symbol)),
            // TODO: Better error here.
            _ => panic!("Cannot add function symbol to a non-global scope!"),
        };

        Ok(())
    }

    pub(crate) fn add_data_symbol(
        &mut self,
        symbol: DataSymbol,
        is_func_param: bool,
    ) -> Result<(), DeclareExistingSymbolError> {
        if self.contains_data_symbol(&symbol) {
            return Err(DeclareExistingSymbolError::new(
                self.name().to_owned(),
                symbol.name().to_owned(),
            ));
        }

        match self {
            Scope::Global { data_symbols, .. } | Scope::Anonymous { data_symbols, .. } => {
                data_symbols.insert(Rc::new(symbol));
            }
            Scope::Function {
                data_symbols,
                stack_frame_local_slot_map,
                stack_frame_param_slot_map,
                ..
            } => {
                let symbol = Rc::new(symbol);
                if is_func_param {
                    stack_frame_param_slot_map.insert(
                        symbol.clone(),
                        STACK_FRAME_PARAM_SLOT_COUNTER.fetch_add(1, Ordering::SeqCst),
                    );
                } else {
                    stack_frame_local_slot_map.insert(
                        symbol.clone(),
                        STACK_FRAME_LOCAL_SLOT_COUNTER.fetch_sub(1, Ordering::SeqCst),
                    );
                }
                data_symbols.insert(symbol);
            }
        };
        Ok(())
    }

    pub(crate) fn data_symbol_for_name(&self, symbol_name: &str) -> Result<Rc<DataSymbol>, UseUndeclaredSymbolError> {
        match self {
            Scope::Global { data_symbols, .. }
            | Scope::Anonymous { data_symbols, .. }
            | Scope::Function { data_symbols, .. } => data_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| symbol.clone())
                .ok_or(UseUndeclaredSymbolError::new(
                    self.name().to_owned(),
                    symbol_name.to_owned(),
                ))
        }
    }

    pub(crate) fn function_symbol_for_name(&self, symbol_name: &str) -> Result<Rc<FunctionSymbol>, UseUndeclaredSymbolError> {
        match self {
            Scope::Global { function_symbols, .. } => function_symbols
                .iter()
                .find(|&symbol| symbol.name() == symbol_name)
                .map(|symbol| symbol.clone())
                .ok_or(UseUndeclaredSymbolError::new(
                    self.name().to_owned(),
                    symbol_name.to_owned(),
                )),
            Scope::Anonymous { .. }
            | Scope::Function { .. } => Err(UseUndeclaredSymbolError::new(
                self.name().to_owned(),
                symbol_name.to_owned(),
                )),
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
    // TODO: Add unit tests
}