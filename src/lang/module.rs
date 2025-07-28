use std::fmt::Debug;

use crate::lang::types::{Builtins, SymbolId, SymbolTable};

pub trait LanguageModule: Debug {
    fn insert_symbols(&self, symbol_table: &mut SymbolTable, builtins: &Builtins, global: SymbolId);
}
