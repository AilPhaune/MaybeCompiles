use crate::lang::{
    module::LanguageModule,
    types::{Builtins, Symbol, SymbolId, SymbolTable, gen_function_t},
};

#[derive(Debug)]
pub struct BooleanModule;

impl BooleanModule {
    pub fn new() -> BooleanModule {
        BooleanModule
    }
}

impl LanguageModule for BooleanModule {
    fn insert_symbols(
        &self,
        symbol_table: &mut SymbolTable,
        builtins: &Builtins,
        global: SymbolId,
    ) {
        // NEGATE FUNCTION
        symbol_table.insert(
            Symbol::Function(gen_function_t(
                "operator!negate",
                builtins.bool_t,
                &[],
                builtins.bool_t,
            )),
            global,
        );
    }
}
