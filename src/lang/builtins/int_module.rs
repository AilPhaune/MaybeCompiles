use std::num::NonZeroU16;

use crate::lang::{
    module::LanguageModule,
    types::{
        BasicType, Builtins, Symbol, SymbolId, SymbolTable, Type, TypedefSymbol, gen_function_t,
    },
};

#[derive(Debug)]
pub struct SignedIntegerModule {
    pub bits: NonZeroU16,
}

impl SignedIntegerModule {
    pub fn new(bits: NonZeroU16) -> Self {
        Self { bits }
    }

    pub fn create(bits: u16) -> Option<Self> {
        NonZeroU16::new(bits).map(SignedIntegerModule::new)
    }
}

fn is_native_width(bits: u16) -> bool {
    match bits {
        64 => true,
        _ => false,
    }
}

fn get_builtin_int(builtins: &Builtins, bits: u16) -> SymbolId {
    match bits {
        64 => builtins.i64_t,
        _ => SymbolId::undefined(),
    }
}

impl LanguageModule for SignedIntegerModule {
    fn insert_symbols(
        &self,
        symbol_table: &mut SymbolTable,
        builtins: &Builtins,
        global: SymbolId,
    ) {
        let type_id = if !is_native_width(self.bits.get()) {
            symbol_table.insert(
                Symbol::TypeDef(TypedefSymbol {
                    parent: global,
                    id: SymbolId::undefined(),
                    name: format!("i{}", self.bits),
                    t: Type::Basic(BasicType::SignedInt(self.bits.get())),
                }),
                global,
            )
        } else {
            get_builtin_int(builtins, self.bits.get())
        };

        // ADD FUNCTION
        symbol_table.insert(
            Symbol::Function(gen_function_t("add", type_id, &[type_id], type_id)),
            global,
        );
        symbol_table.insert(
            Symbol::Function(gen_function_t("operator!add", type_id, &[type_id], type_id)),
            global,
        );

        // PRINT FUNCTION
        symbol_table.insert(
            Symbol::Function(gen_function_t("print", type_id, &[], builtins.void_t)),
            global,
        );
    }
}
