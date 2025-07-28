use std::{collections::HashMap, fmt::Write, hash::Hash, usize};

use crate::lang::{
    ast::{
        Action, BooleanOperator, ComparisonOperator, Declaration, DoType, Expression,
        MainFunctionDeclaration, Statement,
    },
    ir_tree::{
        BuiltinIRError, IRAction, IRActions, IRDeclaration, IRError, IRExpression, IRIfStatement,
        IRNode, IRStatement, IRTypeMainFunction, IRWhileLoop, TypeResolution,
    },
    module::LanguageModule,
    token::IdentifierToken,
};

#[derive(Debug, Clone)]
pub enum BasicType {
    Void,
    SignedInt(u16),
    Boolean,
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub arg_this: SymbolId,
    pub args: Vec<(Option<String>, SymbolId)>,
    pub return_type: SymbolId,
}

pub fn internal_mangle_func(arg_this: SymbolId, args: impl Iterator<Item = SymbolId>) -> String {
    let mut result = format!("@{}", arg_this.get());
    result.push('(');
    for (i, arg) in args.enumerate() {
        if i > 0 {
            result.push(',');
        }
        let _ = result.write_fmt(format_args!("{}", arg.get()));
    }
    result.push(')');
    result
}

impl FunctionType {
    pub fn internal_mangle(&self) -> String {
        internal_mangle_func(self.arg_this, self.args.iter().map(|t| t.1))
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Basic(BasicType),
    Function(Box<FunctionType>),
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub parent: Option<SymbolId>,
    pub id: SymbolId,

    pub symbols: HashMap<String, SymbolId>,
    // prevents accessing locals of parent scopes
    pub barrier: bool,
}

impl Scope {
    pub fn internal_mangle(&self) -> String {
        format!("${}", self.id.get())
    }
}

#[derive(Debug, Clone)]
pub struct VariableSymbol {
    pub parent: SymbolId,
    pub var_t: SymbolId,
    pub name: String,
    pub id: SymbolId,
}

impl VariableSymbol {
    pub fn internal_mangle(&self) -> String {
        self.name.clone()
    }
}

#[derive(Debug, Clone)]
pub struct TypedefSymbol {
    pub parent: SymbolId,
    pub id: SymbolId,
    pub name: String,
    pub t: Type,
}

impl TypedefSymbol {
    pub fn internal_mangle(&self) -> String {
        format!("^{}", self.name)
    }
}

#[derive(Debug, Clone)]
pub struct FunctionSymbol {
    body: Option<SymbolId>,
    func_t: FunctionType,
    parent: SymbolId,
    name: String,
    id: SymbolId,
}

impl FunctionSymbol {
    pub fn internal_mangle(&self) -> String {
        format!("{}{}", self.name, self.func_t.internal_mangle())
    }
}

#[derive(Debug, Clone)]
pub enum Symbol {
    Function(FunctionSymbol),
    Variable(VariableSymbol),
    TypeDef(TypedefSymbol),
    Scope(Scope),
}

impl Symbol {
    /*

    FUNCTIONS: name{`@`this_parameter_type?}({args_type*})
    VARIABLES: name
    SCOPE: `$`{scope_id}
    TYPEDEF: `^`name

     */
    pub fn mangle(&self) -> String {
        match self {
            Symbol::Function(func_sym) => func_sym.internal_mangle(),
            Symbol::Variable(var_sym) => var_sym.internal_mangle(),
            Symbol::Scope(scope_sym) => scope_sym.internal_mangle(),
            Symbol::TypeDef(typedef_sym) => typedef_sym.internal_mangle(),
        }
    }

    fn inserted_as(&mut self, id: SymbolId, parent: SymbolId) {
        match self {
            Symbol::Function(func_sym) => {
                func_sym.parent = parent;
                func_sym.id = id;
            }
            Symbol::Variable(var_sym) => {
                var_sym.parent = parent;
                var_sym.id = id;
            }
            Symbol::Scope(scope_sym) => {
                scope_sym.parent = Some(parent);
                scope_sym.id = id;
            }
            Symbol::TypeDef(typedef_sym) => {
                typedef_sym.parent = parent;
                typedef_sym.id = id;
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(usize);

impl SymbolId {
    pub fn undefined() -> Self {
        Self(usize::MAX)
    }

    pub fn new(id: usize) -> Self {
        Self(id)
    }

    pub fn get(&self) -> usize {
        self.0
    }

    pub fn get_symbol<'a>(&self, symbol_table: &'a SymbolTable) -> Result<&'a Symbol, SymbolId> {
        symbol_table.all_symbols.get(self.0).ok_or(*self)
    }

    pub fn get_symbol_mut<'a>(
        &self,
        symbol_table: &'a mut SymbolTable,
    ) -> Result<&'a mut Symbol, SymbolId> {
        symbol_table.all_symbols.get_mut(self.0).ok_or(*self)
    }

    pub fn get_as_scope<'a>(&self, symbol_table: &'a SymbolTable) -> Result<&'a Scope, SymbolId> {
        match symbol_table.all_symbols.get(self.0) {
            Some(Symbol::Scope(scope)) => Ok(scope),
            _ => Err(*self),
        }
    }

    pub fn get_as_scope_mut<'a>(
        &self,
        symbol_table: &'a mut SymbolTable,
    ) -> Result<&'a mut Scope, SymbolId> {
        match symbol_table.all_symbols.get_mut(self.0) {
            Some(Symbol::Scope(scope)) => Ok(scope),
            _ => Err(*self),
        }
    }

    pub fn get_as_function<'a>(
        &self,
        symbol_table: &'a SymbolTable,
    ) -> Result<&'a FunctionSymbol, SymbolId> {
        match symbol_table.all_symbols.get(self.0) {
            Some(Symbol::Function(func_sym)) => Ok(func_sym),
            _ => Err(*self),
        }
    }

    pub fn get_as_function_mut<'a>(
        &self,
        symbol_table: &'a mut SymbolTable,
    ) -> Result<&'a mut FunctionSymbol, SymbolId> {
        match symbol_table.all_symbols.get_mut(self.0) {
            Some(Symbol::Function(func_sym)) => Ok(func_sym),
            _ => Err(*self),
        }
    }

    pub fn mangle(&self, symbol_table: &SymbolTable) -> Result<String, SymbolId> {
        Ok(self.get_symbol(symbol_table)?.mangle())
    }

    pub fn get_as_variable<'a>(
        &self,
        symbol_table: &'a SymbolTable,
    ) -> Result<&'a VariableSymbol, SymbolId> {
        match symbol_table.all_symbols.get(self.0) {
            Some(Symbol::Variable(var_sym)) => Ok(var_sym),
            _ => Err(*self),
        }
    }

    pub fn get_as_variable_mut<'a>(
        &self,
        symbol_table: &'a mut SymbolTable,
    ) -> Result<&'a mut VariableSymbol, SymbolId> {
        match symbol_table.all_symbols.get_mut(self.0) {
            Some(Symbol::Variable(var_sym)) => Ok(var_sym),
            _ => Err(*self),
        }
    }

    pub fn is_static(&self, symbol_table: &SymbolTable) -> Result<bool, SymbolId> {
        match self.get_symbol(symbol_table)? {
            Symbol::Variable(_) => Ok(false),
            Symbol::TypeDef(_) => Ok(true),
            Symbol::Function(_) => Ok(true),
            Symbol::Scope(_) => Ok(false),
        }
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    all_symbols: Vec<Symbol>,
    named_symbols: HashMap<String, usize>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            all_symbols: vec![],
            named_symbols: HashMap::new(),
        }
    }

    pub fn insert_top_scope(&mut self, mut scope: Scope) -> SymbolId {
        let len = self.all_symbols.len();
        scope.parent = None;
        scope.id = SymbolId(len);
        self.all_symbols.push(Symbol::Scope(scope));
        SymbolId(len)
    }

    pub fn insert(&mut self, mut symbol: Symbol, parent: SymbolId) -> SymbolId {
        let len = self.all_symbols.len();
        symbol.inserted_as(SymbolId(len), parent);

        if let Ok(scope) = parent.get_as_scope_mut(self) {
            scope.symbols.insert(symbol.mangle(), SymbolId(len));
        }

        self.all_symbols.push(symbol);

        SymbolId(len)
    }

    pub fn set_name(&mut self, name: String, index: SymbolId) -> bool {
        if self.named_symbols.contains_key(&name) {
            return false;
        }
        self.named_symbols.insert(name, index.get());
        true
    }

    pub fn get(&self, name: &str) -> Option<&Symbol> {
        self.named_symbols
            .get(name)
            .and_then(|index| self.all_symbols.get(*index))
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut Symbol> {
        self.named_symbols
            .get(name)
            .and_then(|index| self.all_symbols.get_mut(*index))
    }
}

#[derive(Debug)]
pub struct Builtins {
    pub i64_t: SymbolId,
    pub bool_t: SymbolId,
    pub void_t: SymbolId,
}

#[derive(Debug)]
pub struct TypeCheckingContext<'a> {
    pub scope_stack: Vec<SymbolId>,
    pub symbol_table: SymbolTable,
    pub global: SymbolId,
    pub main_function: Option<SymbolId>,
    pub builtins: Builtins,

    pub modules: Vec<&'a dyn LanguageModule>,
}

fn gen_bool_t() -> TypedefSymbol {
    TypedefSymbol {
        parent: SymbolId(0),
        id: SymbolId(0),
        name: "bool".to_string(),
        t: Type::Basic(BasicType::Boolean),
    }
}

fn gen_int_type(bits: u16) -> TypedefSymbol {
    TypedefSymbol {
        parent: SymbolId(0),
        id: SymbolId(0),
        name: format!("i{}", bits),
        t: Type::Basic(BasicType::SignedInt(bits)),
    }
}

fn gen_void_t() -> TypedefSymbol {
    TypedefSymbol {
        parent: SymbolId(0),
        id: SymbolId(0),
        name: "void".to_string(),
        t: Type::Basic(BasicType::Void),
    }
}

pub fn gen_function_t(
    name: &str,
    arg_this: SymbolId,
    params: &[SymbolId],
    return_type: SymbolId,
) -> FunctionSymbol {
    FunctionSymbol {
        name: name.to_string(),
        parent: SymbolId(0),
        id: SymbolId(0),
        body: None,
        func_t: FunctionType {
            arg_this,
            args: params.iter().map(|t| (None, *t)).collect(),
            return_type,
        },
    }
}

impl<'a> TypeCheckingContext<'a> {
    pub fn new_with_builtins(modules: Vec<&'a dyn LanguageModule>) -> Self {
        let mut symbt = SymbolTable::new();

        let glob_id = symbt.insert_top_scope(Scope {
            symbols: HashMap::new(),
            barrier: true,
            parent: None,
            id: SymbolId(0),
        });

        let i64_t = symbt.insert(Symbol::TypeDef(gen_int_type(64)), glob_id);
        let bool_t = symbt.insert(Symbol::TypeDef(gen_bool_t()), glob_id);
        let void_t = symbt.insert(Symbol::TypeDef(gen_void_t()), glob_id);

        for module in modules.iter() {
            module.insert_symbols(
                &mut symbt,
                &Builtins {
                    i64_t,
                    bool_t,
                    void_t,
                },
                glob_id,
            );
        }

        Self {
            scope_stack: vec![glob_id],
            global: glob_id,
            symbol_table: symbt,
            main_function: None,
            builtins: Builtins {
                i64_t,
                bool_t,
                void_t,
            },
            modules,
        }
    }

    fn define_function(
        &mut self,
        func_type: FunctionType,
        name: String,
    ) -> Result<(SymbolId, SymbolId), IRError> {
        if self.peek_scope()?.symbols.contains_key(&name) {
            return Err(IRError::DuplicateFunctionName(name.clone()));
        }

        let body_scope = Scope {
            parent: None,
            id: SymbolId(0),
            symbols: HashMap::new(),
            barrier: true, // is a function, can't access higher up locals
        };

        let func_id = self.symbol_table.insert(
            Symbol::Function(FunctionSymbol {
                func_t: func_type.clone(),
                parent: SymbolId(0),
                name: name.clone(),
                id: SymbolId(0),
                body: None,
            }),
            self.peek_id()?,
        );

        for (arg_name, arg_t) in func_type.args.into_iter() {
            let Some(arg_name) = arg_name else {
                return Err(IRError::IllegalUnnamedArgument);
            };
            if &arg_name == "this" {
                return Err(IRError::IllegalArgumentName(arg_name.clone()));
            }
            if body_scope.symbols.contains_key(&arg_name) {
                return Err(IRError::DuplicateArgumentName(arg_name.clone()));
            }
            self.symbol_table.insert(
                Symbol::Variable(VariableSymbol {
                    parent: SymbolId(0),
                    id: SymbolId(0),
                    var_t: arg_t,
                    name: arg_name,
                }),
                func_id,
            );
        }

        let body_id = self.symbol_table.insert(Symbol::Scope(body_scope), func_id);

        func_id
            .get_as_function_mut(&mut self.symbol_table)
            .map_err(|i| IRError::BuiltinError(BuiltinIRError::IllegalSymbolInScopeStack(i)))?
            .body = Some(body_id);

        self.peek_scope_mut()?.symbols.insert(name, func_id);

        Ok((func_id, body_id))
    }

    fn push(&mut self, id: SymbolId) {
        self.scope_stack.push(id);
    }

    fn pop(&mut self) -> Option<SymbolId> {
        self.scope_stack.pop()
    }

    fn peek(&self) -> Option<SymbolId> {
        self.scope_stack.last().copied()
    }

    fn peek_id(&self) -> Result<SymbolId, IRError> {
        self.peek().ok_or(IRError::UnscopedAccess)
    }

    fn peek_scope(&self) -> Result<&Scope, IRError> {
        self.peek_id()?
            .get_as_scope(&self.symbol_table)
            .map_err(|i| IRError::BuiltinError(BuiltinIRError::IllegalSymbolInScopeStack(i)))
    }

    fn peek_scope_mut(&mut self) -> Result<&mut Scope, IRError> {
        self.peek_id()?
            .get_as_scope_mut(&mut self.symbol_table)
            .map_err(|i| IRError::BuiltinError(BuiltinIRError::IllegalSymbolInScopeStack(i)))
    }

    fn lookup(&self, name: &str) -> Result<SymbolId, IRError> {
        let mut barriered = false;

        for scope_id in self.scope_stack.iter().rev() {
            if let Ok(scope) = scope_id.get_as_scope(&self.symbol_table) {
                if scope.barrier {
                    barriered = true;
                }

                if let Some(id) = scope.symbols.get(name) {
                    if !barriered
                        || id
                            .is_static(&self.symbol_table)
                            .map_err(|id| IRError::InvalidSymbolId(id))?
                    {
                        return Ok(*id);
                    } else {
                        return Err(IRError::IllegalAccess(name.to_string(), *id));
                    }
                }
            }
        }

        // TODO: implement parent lookup
        self.peek_scope().and_then(|scope| {
            scope
                .symbols
                .get(name)
                .copied()
                .ok_or_else(|| IRError::UnknownIdentifier(name.to_string()))
        })
    }

    fn lookup_function(
        &self,
        name: &str,
        this_arg: SymbolId,
        arg_types: &[SymbolId],
    ) -> Result<SymbolId, IRError> {
        let mangled = format!(
            "{}{}",
            name,
            internal_mangle_func(this_arg, arg_types.iter().copied())
        );

        for scope_id in self.scope_stack.iter().rev() {
            if let Ok(scope) = scope_id.get_as_scope(&self.symbol_table) {
                if let Some(func_id) = scope.symbols.get(&mangled) {
                    if func_id.get_as_function(&self.symbol_table).is_ok() {
                        return Ok(*func_id);
                    }
                }
            }
        }

        return Err(IRError::UnknownIdentifier(mangled));
    }

    pub fn construct_ir_identifier(
        &mut self,
        idt: IdentifierToken,
    ) -> Result<IRNode<IRExpression>, IRError> {
        let id = self.lookup(&idt.value)?;
        let sym = id
            .get_symbol(&self.symbol_table)
            .map_err(IRError::InvalidSymbolId)?;

        let expr_type = match sym {
            Symbol::Variable(t) => t.var_t,
            Symbol::Scope(_) => return Err(IRError::InvalidReferableSymbol(id)),
            Symbol::TypeDef(_) => return Err(IRError::InvalidReferableSymbol(id)),
            // TODO: implement getting function pointers probably ?
            Symbol::Function(..) => return Err(IRError::InvalidReferableSymbol(id)),
        };

        Ok(IRNode {
            value: Box::new(IRExpression::Identifier(idt, id)),
            expr_type: TypeResolution::Resolved(expr_type),
        })
    }

    pub fn construct_ir_do_until(
        &mut self,
        expr: Expression,
        until_expr: Expression,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let expr = self.construct_ir_expression(expr)?;

        let negated = self.construct_ir_boolean_negate(until_expr)?;

        if negated.expr_type != TypeResolution::Resolved(self.builtins.bool_t) {
            return Err(IRError::TypeMismatch(
                TypeResolution::Resolved(self.builtins.bool_t),
                negated.expr_type,
            ));
        }

        Ok(IRNode {
            value: Box::new(IRStatement::WhileLoop(IRWhileLoop {
                condition: negated.value,
                body: expr.value,
            })),
            // `do { ... } until (condition);` aka `while (!condition) {...}` loop is always void
            expr_type: TypeResolution::Resolved(self.builtins.void_t),
        })
    }

    pub fn construct_ir_do_unless(
        &mut self,
        expr: Expression,
        unless_expr: Expression,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let expr = self.construct_ir_expression(expr)?;

        let negated = self.construct_ir_boolean_negate(unless_expr)?;

        if negated.expr_type != TypeResolution::Resolved(self.builtins.bool_t) {
            return Err(IRError::TypeMismatch(
                TypeResolution::Resolved(self.builtins.bool_t),
                negated.expr_type,
            ));
        }

        Ok(IRNode {
            value: Box::new(IRStatement::IfStatement(IRIfStatement {
                if_condition: negated.value,
                if_body: expr.value,
                else_ifs: Vec::new(),
                else_body: None,
            })),
            expr_type: TypeResolution::Resolved(self.builtins.void_t),
        })
    }

    pub fn construct_ir_do_statement(
        &mut self,
        expr: Expression,
        do_type: DoType,
    ) -> Result<IRNode<IRStatement>, IRError> {
        match do_type {
            DoType::Unless(unless_expr) => Ok(self.construct_ir_do_unless(expr, *unless_expr)?),
            DoType::Until(until_expr) => Ok(self.construct_ir_do_until(expr, *until_expr)?),
        }
    }

    pub fn construct_ir_action_return(
        &mut self,
        stmt: Statement,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let mut irstmt = self.construct_ir_statement(stmt)?;

        match &mut *irstmt.value {
            IRStatement::Actions(iraction) => {
                iraction.actions.push(IRAction::ReturnIt);
                iraction.type_stack.clear();
                irstmt.expr_type = TypeResolution::Resolved(self.builtins.void_t);
                Ok(irstmt)
            }
            _ => Ok(IRNode {
                value: Box::new(IRStatement::Actions(IRActions {
                    statement: irstmt.value,
                    actions: vec![IRAction::ReturnIt],
                    type_stack: vec![], // nothing, we returned the value
                })),
                expr_type: TypeResolution::Resolved(self.builtins.void_t),
            }),
        }
    }

    pub fn construct_ir_action_discard(
        &mut self,
        stmt: Statement,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let mut irstmt = self.construct_ir_statement(stmt)?;

        match &mut *irstmt.value {
            IRStatement::Actions(iraction) => {
                iraction.actions.push(IRAction::DiscardIt);

                // Check if it's discardable
                if let Some(_) = iraction.type_stack.pop() {
                    // Discarded the value by removing it from the stack
                    irstmt.expr_type = TypeResolution::Resolved(
                        *iraction.type_stack.last().unwrap_or(&self.builtins.void_t),
                    );
                    Ok(irstmt)
                } else {
                    // No value to discard
                    Err(IRError::InvalidDiscardAction)
                }
            }
            _ => Ok(IRNode {
                value: Box::new(IRStatement::Actions(IRActions {
                    statement: irstmt.value,
                    actions: vec![IRAction::DiscardIt],
                    type_stack: vec![], // nothing, we discarded the value
                })),
                expr_type: TypeResolution::Resolved(self.builtins.void_t),
            }),
        }
    }

    pub fn construct_ir_action_use_on_it(
        &mut self,
        stmt: Statement,
        func: IdentifierToken,
        args: Vec<Expression>,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let mut irstmt = self.construct_ir_statement(stmt)?;

        let mut irargs = Vec::new();
        let mut args_t = Vec::new();
        for arg in args {
            let irarg = self.construct_ir_expression(arg)?;
            irargs.push(*irarg.value);
            args_t.push(irarg.expr_type.type_id_now_or_err()?);
        }

        let func_id =
            self.lookup_function(&func.value, irstmt.expr_type.type_id_now_or_err()?, &args_t)?;

        let func_rt_type = func_id
            .get_as_function(&self.symbol_table)
            .map_err(|id| IRError::InvalidFunctionSymbol(id))?
            .func_t
            .return_type;

        match &mut *irstmt.value {
            IRStatement::Actions(iractions) => {
                iractions
                    .actions
                    .push(IRAction::UseOnIt(func, func_id, irargs));

                iractions.type_stack.push(func_rt_type);
                irstmt.expr_type = TypeResolution::Resolved(func_rt_type);

                Ok(irstmt)
            }
            _ => Ok(IRNode {
                value: Box::new(IRStatement::Actions(IRActions {
                    statement: irstmt.value,
                    actions: vec![IRAction::UseOnIt(func, func_id, irargs)],
                    type_stack: vec![irstmt.expr_type.type_id_now_or_err()?, func_rt_type],
                })),
                expr_type: TypeResolution::Resolved(func_rt_type),
            }),
        }
    }

    pub fn construct_ir_action_call_it(
        &mut self,
        stmt: Statement,
        name: IdentifierToken,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let mut irstmt = self.construct_ir_statement(stmt)?;

        let var_id = match self.lookup(&name.value) {
            Ok(i) => match i.get_as_variable(&self.symbol_table) {
                Ok(v) => {
                    if v.var_t != irstmt.expr_type.type_id_now_or_err()? {
                        return Err(IRError::TypeMismatch(
                            TypeResolution::Resolved(v.var_t),
                            irstmt.expr_type,
                        ));
                    } else {
                        v.id
                    }
                }
                Err(_) => return Err(IRError::ReferedSymbolIsNotVariable(i)),
            },
            Err(_) => {
                let var_id = self.symbol_table.insert(
                    Symbol::Variable(match irstmt.expr_type {
                        TypeResolution::Unresolved => {
                            return Err(IRError::TypeShouldBeResolved(irstmt.expr_type));
                        }
                        TypeResolution::Resolved(t) => VariableSymbol {
                            name: name.value.clone(),
                            parent: SymbolId(0),
                            id: SymbolId(0),
                            var_t: t,
                        },
                    }),
                    self.peek_id()?,
                );
                let scope = self.peek_scope_mut()?;
                scope.symbols.insert(name.value.clone(), var_id);
                var_id
            }
        };

        match &mut *irstmt.value {
            IRStatement::Actions(iractions) => {
                iractions.actions.push(IRAction::CallIt(name, var_id));
                // CallIt doesn't consume nor produce any value, it just allows to directly use the value that was saved in the variable
                Ok(irstmt)
            }
            _ => Ok(IRNode {
                value: Box::new(IRStatement::Actions(IRActions {
                    statement: irstmt.value,
                    actions: vec![IRAction::CallIt(name, var_id)],
                    type_stack: vec![irstmt.expr_type.type_id_now_or_err()?],
                })),
                expr_type: irstmt.expr_type,
            }),
        }
    }

    pub fn construct_ir_action(
        &mut self,
        stmt: Statement,
        action: Action,
    ) -> Result<IRNode<IRStatement>, IRError> {
        match action {
            Action::ReturnIt => Ok(self.construct_ir_action_return(stmt)?),
            Action::DiscardIt => Ok(self.construct_ir_action_discard(stmt)?),
            Action::UseOnIt(func, args) => {
                Ok(self.construct_ir_action_use_on_it(stmt, func, args)?)
            }
            Action::CallIt(name) => Ok(self.construct_ir_action_call_it(stmt, name)?),
        }
    }

    pub fn construct_ir_call(
        &mut self,
        func: IdentifierToken,
        args: Vec<Expression>,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let mut irargs = Vec::new();
        let mut args_t = Vec::new();
        for arg in args {
            let irarg = self.construct_ir_expression(arg)?;
            irargs.push(*irarg.value);
            args_t.push(irarg.expr_type.type_id_now_or_err()?);
        }

        let f_id = self.lookup_function(&func.value, self.builtins.void_t, &[])?;

        let f_sym = f_id
            .get_symbol(&self.symbol_table)
            .map_err(IRError::InvalidSymbolId)?;

        let func_t = match f_sym {
            Symbol::Function(func_s) => &func_s.func_t,
            _ => return Err(IRError::ReferedSymbolIsNotCallable(f_id)),
        };

        let ret_t = func_t.return_type;

        Ok(IRNode {
            value: Box::new(IRStatement::Take(IRExpression::Call(
                Some(func),
                f_id,
                irargs,
            ))),
            expr_type: TypeResolution::Resolved(ret_t),
        })
    }

    pub fn construct_ir_take_statement(
        &mut self,
        expr: Expression,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let irexpr = self.construct_ir_expression(expr)?;

        Ok(IRNode {
            value: Box::new(IRStatement::Take(*irexpr.value)),
            expr_type: irexpr.expr_type,
        })
    }

    pub fn construct_ir_statement(
        &mut self,
        stmt: Statement,
    ) -> Result<IRNode<IRStatement>, IRError> {
        match stmt {
            Statement::VoidDeclaration(declaration) => Ok(IRNode {
                value: Box::new(IRStatement::VoidDeclaration(
                    self.construct_ir_declaration(*declaration)?.value,
                )),
                expr_type: TypeResolution::Resolved(self.builtins.void_t),
            }),
            Statement::Take(expr) => Ok(self.construct_ir_take_statement(*expr)?),
            Statement::Do(expr, do_type) => Ok(self.construct_ir_do_statement(*expr, do_type)?),
            Statement::Action(stmt, action) => Ok(self.construct_ir_action(*stmt, action)?),
            Statement::Call(func, args) => Ok(self.construct_ir_call(func, args)?),
        }
    }

    pub fn construct_ir_block(
        &mut self,
        stmts: Vec<Statement>,
    ) -> Result<IRNode<IRExpression>, IRError> {
        let block_id = self.symbol_table.insert(
            Symbol::Scope(Scope {
                symbols: HashMap::new(),
                id: SymbolId(0),
                barrier: false,
                parent: None,
            }),
            self.peek_id()?,
        );
        self.push(block_id);

        let mut ir_stmts = Vec::new();
        for stmt in stmts {
            let irstmt = self.construct_ir_statement(stmt)?;
            ir_stmts.push(*irstmt.value);
            // TODO: Check for return statments if they all return the same type, and if all code paths end up returning
        }

        self.pop();

        Ok(IRNode {
            value: Box::new(IRExpression::Block(ir_stmts, block_id)),
            // FIXME: This is wrong, i'm lazy
            expr_type: TypeResolution::Resolved(self.builtins.void_t),
        })
    }

    pub fn construct_ir_comparison(
        &mut self,
        l: Expression,
        op: ComparisonOperator,
        r: Expression,
    ) -> Result<IRNode<IRExpression>, IRError> {
        let l = self.construct_ir_expression(l)?;
        let r = self.construct_ir_expression(r)?;

        let l_type = l.expr_type.type_id_now_or_err()?;
        let r_type = r.expr_type.type_id_now_or_err()?;

        let func_id =
            self.lookup_function(op.internal_operator_function_magled(), l_type, &[r_type])?;

        let ret_t = func_id
            .get_as_function(&self.symbol_table)
            .map_err(|e| IRError::InvalidFunctionSymbol(e))?
            .func_t
            .return_type;

        Ok(IRNode {
            value: Box::new(IRExpression::Call(None, func_id, vec![*l.value, *r.value])),
            expr_type: TypeResolution::Resolved(ret_t),
        })
    }

    pub fn construct_ir_boolean_op(
        &mut self,
        l: Expression,
        op: BooleanOperator,
        r: Expression,
    ) -> Result<IRNode<IRExpression>, IRError> {
        let l = self.construct_ir_expression(l)?;
        let r = self.construct_ir_expression(r)?;

        let l_type = l.expr_type.type_id_now_or_err()?;
        let r_type = r.expr_type.type_id_now_or_err()?;

        let func_id =
            self.lookup_function(op.internal_operator_function_magled(), l_type, &[r_type])?;

        let ret_t = func_id
            .get_as_function(&self.symbol_table)
            .map_err(|e| IRError::InvalidFunctionSymbol(e))?
            .func_t
            .return_type;

        Ok(IRNode {
            value: Box::new(IRExpression::Call(None, func_id, vec![*l.value, *r.value])),
            expr_type: TypeResolution::Resolved(ret_t),
        })
    }

    pub fn construct_ir_boolean_negate(
        &mut self,
        expr: Expression,
    ) -> Result<IRNode<IRExpression>, IRError> {
        let expr = self.construct_ir_expression(expr)?;

        let func_id =
            self.lookup_function("operator!negate", expr.expr_type.type_id_now_or_err()?, &[])?;

        let ret_t = func_id
            .get_as_function(&self.symbol_table)
            .map_err(|e| IRError::InvalidFunctionSymbol(e))?
            .func_t
            .return_type;

        Ok(IRNode {
            value: Box::new(IRExpression::Call(None, func_id, vec![*expr.value])),
            expr_type: TypeResolution::Resolved(ret_t),
        })
    }

    pub fn construct_ir_expression(
        &mut self,
        expr: Expression,
    ) -> Result<IRNode<IRExpression>, IRError> {
        match expr {
            Expression::IntI64(val) => Ok(IRNode {
                value: Box::new(IRExpression::IntI64(val)),
                expr_type: TypeResolution::Resolved(self.builtins.i64_t),
            }),
            Expression::Identifier(idt) => Ok(self.construct_ir_identifier(idt)?),
            Expression::Comparison(l, op, r) => Ok(self.construct_ir_comparison(*l, op, *r)?),
            Expression::Boolean(l, op, r) => Ok(self.construct_ir_boolean_op(*l, op, *r)?),
            Expression::BooleanNegate(expr) => Ok(self.construct_ir_boolean_negate(*expr)?),
            Expression::Block(stmts) => Ok(self.construct_ir_block(stmts)?),
        }
    }

    pub fn construct_ir_main_decl(
        &mut self,
        main_decl: MainFunctionDeclaration,
    ) -> Result<IRNode<IRTypeMainFunction>, IRError> {
        if let Some(id) = self.main_function {
            return Err(IRError::MultipleMainFunctionDeclarations(id));
        }

        let (func_id, body_id) = self.define_function(
            FunctionType {
                arg_this: self.builtins.void_t,
                args: Vec::new(),
                return_type: self.builtins.void_t,
            },
            "main".to_string(),
        )?;

        self.main_function = Some(func_id);
        self.push(body_id);

        let ir_body = self.construct_ir_expression(main_decl.body)?;

        self.pop();

        Ok(IRNode {
            value: Box::new(IRTypeMainFunction {
                func_id,
                body_scope_id: body_id,
                body: ir_body.value,
            }),
            expr_type: TypeResolution::Resolved(self.builtins.void_t),
        })
    }

    pub fn construct_ir_declaration(
        &mut self,
        decl: Declaration,
    ) -> Result<IRNode<IRDeclaration>, IRError> {
        match decl {
            Declaration::MainFunction(main_decl) => Ok(IRNode {
                value: Box::new(IRDeclaration::MainFunction(
                    self.construct_ir_main_decl(main_decl)?.value,
                )),
                expr_type: TypeResolution::Resolved(self.builtins.void_t),
            }),
            _ => todo!("construct_ir_declaration"),
        }
    }
}
