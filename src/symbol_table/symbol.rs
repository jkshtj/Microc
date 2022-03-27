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

    /// Represents a global symbol declared in
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
        // FunctionDataSymbol(FunctionDataSymbol),
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

    #[derive(Debug, Eq, Clone, PartialEq, Hash, derive_more::Display)]
    pub enum FunctionDataSymbolType {
        #[display(fmt = "P")]
        Parameter,
        #[display(fmt = "L")]
        Local,
    }

    /// Represents a symbol in the context of a
    /// function. The symbol is either a function
    /// parameter or a local variable and can be
    /// an int or a float.
    #[derive(Debug, PartialEq, Clone, Hash, Eq, derive_more::Display)]
    pub enum FunctionDataSymbol {
        #[display(fmt = "name: {}{} type INT\n", symbol_type, index)]
        Int {
            symbol_type: FunctionDataSymbolType,
            index: u32,
        },
        #[display(fmt = "name: {}{} type FLOAT\n", symbol_type, index)]
        Float {
            symbol_type: FunctionDataSymbolType,
            index: u32,
        },
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
        pub fn new(name: String, return_type: ReturnType, param_list: Vec<NumType>) -> Self {
            Self {
                name,
                return_type,
                param_list
            }
        }

        pub fn name(&self) -> &str {
            &self.name
        }
    }
}
