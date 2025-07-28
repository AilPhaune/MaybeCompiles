use std::{collections::HashMap, fmt::Write, hash::Hash, usize};

use crate::lang::{
    ast::{
        Action, BooleanOperator, ComparisonOperator, Declaration, DoType, Expression,
        MainFunctionDeclaration, Statement,
    },
    ir_tree::{
        BuiltinIRError, IRAction, IRDeclaration, IRError, IRExpression, IRNode, IRStatement,
        IRTypeMainFunction, IRWhileLoop, TypeResolution,
    },
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
    pub arg_this: Option<SymbolId>,
    pub args: Vec<(Option<String>, SymbolId)>,
    pub return_type: SymbolId,
}

impl FunctionType {
    pub fn internal_mangle(&self) -> String {
        let mut result = String::new();
        if let Some(this) = self.arg_this {
            let _ = result.write_fmt(format_args!("@{}", this.0));
        }
        result.push('(');
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                result.push(',');
            }
            let _ = result.write_fmt(format_args!("{}", arg.1.get()));
        }
        result.push(')');
        result
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    Basic(BasicType),
    Function(Box<FunctionType>),
}

#[derive(Debug, Clone)]
pub struct Scope {
    parent: Option<SymbolId>,
    id: SymbolId,

    symbols: HashMap<String, SymbolId>,
    // prevents accessing locals of parent scopes
    barrier: bool,
}

impl Scope {
    pub fn internal_mangle(&self) -> String {
        format!("${}", self.id.get())
    }
}

#[derive(Debug, Clone)]
pub struct VariableSymbol {
    parent: SymbolId,
    var_t: SymbolId,
    name: String,
    id: SymbolId,
}

impl VariableSymbol {
    pub fn internal_mangle(&self) -> String {
        self.name.clone()
    }
}

#[derive(Debug, Clone)]
pub struct TypedefSymbol {
    parent: SymbolId,
    id: SymbolId,
    name: String,
    t: Type,
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

    pub operator_negate_bool_f: SymbolId,
    pub operator_bool_or_bool_f: SymbolId,
    pub operator_bool_and_bool_f: SymbolId,
}

#[derive(Debug)]
pub struct TypeCheckingContext {
    pub scope_stack: Vec<SymbolId>,
    pub symbol_table: SymbolTable,
    pub global: SymbolId,
    pub main_function: Option<SymbolId>,
    pub builtins: Builtins,
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

fn gen_function_t(
    name: &str,
    arg_this: Option<SymbolId>,
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

impl TypeCheckingContext {
    pub fn new_with_builtins() -> Self {
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

        let operator_negate_bool_f = symbt.insert(
            Symbol::Function(gen_function_t("operator!negate", Some(bool_t), &[], bool_t)),
            glob_id,
        );
        let operator_bool_or_bool_f = symbt.insert(
            Symbol::Function(gen_function_t(
                "operator!bool_or",
                Some(bool_t),
                &[bool_t],
                bool_t,
            )),
            glob_id,
        );
        let operator_bool_and_bool_f = symbt.insert(
            Symbol::Function(gen_function_t(
                "operator!bool_and",
                Some(bool_t),
                &[bool_t],
                bool_t,
            )),
            glob_id,
        );

        Self {
            scope_stack: vec![glob_id],
            global: glob_id,
            symbol_table: symbt,
            main_function: None,
            builtins: Builtins {
                i64_t,
                bool_t,
                void_t,

                operator_negate_bool_f,
                operator_bool_or_bool_f,
                operator_bool_and_bool_f,
            },
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
        // TODO: implement parent lookup
        self.peek_scope().and_then(|scope| {
            scope
                .symbols
                .get(name)
                .copied()
                .ok_or_else(|| IRError::UnknownIdentifier(name.to_string()))
        })
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
        // TODO
        todo!("construct_ir_do_unless")
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
        // TODO
        todo!("construct_ir_action_return")
    }

    pub fn construct_ir_action_discard(
        &mut self,
        stmt: Statement,
    ) -> Result<IRNode<IRStatement>, IRError> {
        // TODO: Check that statement is discardable

        let mut irstmt = self.construct_ir_statement(stmt)?;

        match &mut *irstmt.value {
            IRStatement::Actions(_, actions) => {
                actions.push(IRAction::DiscardIt);

                // FIXME: Check expr_type to see if it's discardable, and update expr_type

                Ok(irstmt)
            }
            _ => Ok(IRNode {
                value: Box::new(IRStatement::Actions(
                    irstmt.value,
                    vec![IRAction::DiscardIt],
                )),
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

        // FIXME: Find actual function
        let func_id = SymbolId(usize::MAX);

        let mut irargs = Vec::new();
        for arg in args {
            irargs.push(*self.construct_ir_expression(arg)?.value);
        }
        // TODO: Check that arguments are valid (count + types)

        match &mut *irstmt.value {
            IRStatement::Actions(_, actions) => {
                actions.push(IRAction::UseOnIt(func, func_id, irargs));

                // FIXME: This is wrong, i'm lazy
                irstmt.expr_type = TypeResolution::Unresolved;

                Ok(irstmt)
            }
            _ => {
                Ok(IRNode {
                    value: Box::new(IRStatement::Actions(
                        irstmt.value,
                        vec![IRAction::UseOnIt(func, func_id, irargs)],
                    )),
                    // FIXME: This is wrong, i'm lazy
                    expr_type: TypeResolution::Unresolved,
                })
            }
        }
    }

    pub fn construct_ir_action_call_it(
        &mut self,
        stmt: Statement,
        name: IdentifierToken,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let mut irstmt = self.construct_ir_statement(stmt)?;

        let var_id = match self.lookup(&name.value) {
            Ok(i) => {
                // TODO: check if it's a variable, and if it has the right type
                i
            }
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
            IRStatement::Actions(_, actions) => {
                actions.push(IRAction::CallIt(name, var_id));
                Ok(irstmt)
            }
            _ => Ok(IRNode {
                value: Box::new(IRStatement::Actions(
                    irstmt.value,
                    vec![IRAction::CallIt(name, var_id)],
                )),
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
        // TODO: Implement function lookup for overloads
        let f_id = self.lookup(&func.value)?;

        let f_sym = f_id
            .get_symbol(&self.symbol_table)
            .map_err(IRError::InvalidSymbolId)?;

        let func_t = match f_sym {
            Symbol::Function(func_s) => &func_s.func_t,
            _ => return Err(IRError::ReferedSymbolIsNotCallable(f_id)),
        };

        let ret_t = func_t.return_type;

        // TODO: Check that function is callable, and that arguments are valid (count + types)
        let mut irargs = Vec::new();
        for arg in args {
            irargs.push(*self.construct_ir_expression(arg)?.value);
        }

        Ok(IRNode {
            value: Box::new(IRStatement::Take(IRExpression::Call(func, f_id, irargs))),
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
        let mut ir_stmts = Vec::new();
        for stmt in stmts {
            let irstmt = self.construct_ir_statement(stmt)?;
            ir_stmts.push(*irstmt.value);
            // TODO: Check for return statments if they all return the same type, and if all code paths end up returning
        }
        Ok(IRNode {
            value: Box::new(IRExpression::Block(ir_stmts)),
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

        // TODO: Check types of `l` and `r`

        Ok(IRNode {
            value: Box::new(IRExpression::Comparison(l.value, op, r.value)),
            expr_type: TypeResolution::Resolved(self.builtins.bool_t),
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

        // TODO: Check types of `l` and `r`

        Ok(IRNode {
            value: Box::new(IRExpression::BooleanOp(l.value, op, r.value)),
            expr_type: TypeResolution::Resolved(self.builtins.bool_t),
        })
    }

    pub fn construct_ir_boolean_negate(
        &mut self,
        expr: Expression,
    ) -> Result<IRNode<IRExpression>, IRError> {
        let expr = self.construct_ir_expression(expr)?;

        // Check if expression can be negated and use correct function

        Ok(IRNode {
            value: Box::new(IRExpression::BooleanNegate(expr.value)),
            expr_type: expr.expr_type,
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
                arg_this: None,
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
