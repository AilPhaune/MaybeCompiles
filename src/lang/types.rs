use std::{collections::HashMap, usize};

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

#[derive(Debug)]
pub enum BasicType {
    Void,
    IntI64,
    Boolean,
}

#[derive(Debug)]
pub struct FunctionType {
    pub param_this: Option<SymbolId>,
    pub args: Vec<(String, SymbolId)>,
    pub return_type: SymbolId,
}

#[derive(Debug)]
pub enum Type {
    Basic(BasicType),
    Function(Box<FunctionType>),
}

#[derive(Debug)]
pub struct Scope {
    symbols: HashMap<String, SymbolId>,
    // prevents accessing locals of parent scopes
    barrier: bool,
}

#[derive(Debug)]
pub enum Symbol {
    TypeDef(Type),
    Variable(SymbolId),
    Scope(Scope),
    Function(FunctionType, SymbolId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    pub fn insert(&mut self, symbol: Symbol) -> SymbolId {
        let len = self.all_symbols.len();
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

    pub negate_bool_f: SymbolId,
}

#[derive(Debug)]
pub struct TypeCheckingContext {
    pub scope_stack: Vec<SymbolId>,
    pub symbol_table: SymbolTable,
    pub global: SymbolId,
    pub main_function: Option<SymbolId>,
    pub builtins: Builtins,
}

impl TypeCheckingContext {
    pub fn new_with_builtins() -> Self {
        let mut symbt = SymbolTable::new();

        let i64_t = symbt.insert(Symbol::TypeDef(Type::Basic(BasicType::IntI64)));
        let bool_t = symbt.insert(Symbol::TypeDef(Type::Basic(BasicType::Boolean)));
        let void_t = symbt.insert(Symbol::TypeDef(Type::Basic(BasicType::Void)));

        let negate_bool_f = symbt.insert(Symbol::Function(
            FunctionType {
                param_this: None,
                args: vec![],
                return_type: bool_t,
            },
            bool_t,
        ));
        symbt.set_name("negate_bool".to_string(), negate_bool_f);

        let glob_id = symbt.insert(Symbol::Scope(Scope {
            symbols: HashMap::from([
                ("i64".to_string(), i64_t),
                ("bool".to_string(), bool_t),
                ("void".to_string(), void_t),
            ]),
            barrier: true,
        }));

        symbt.set_name("global".to_string(), glob_id);

        Self {
            scope_stack: vec![glob_id],
            global: glob_id,
            symbol_table: symbt,
            main_function: None,
            builtins: Builtins {
                i64_t,
                bool_t,
                void_t,

                negate_bool_f,
            },
        }
    }

    fn unchecked_define_function(
        &mut self,
        func_type: FunctionType,
    ) -> Result<(SymbolId, SymbolId), IRError> {
        let body_scope = Scope {
            symbols: HashMap::new(),
            barrier: true, // is a function, can't access higher up locals
        };

        for (arg_name, arg_t) in func_type.args.iter() {
            if arg_name == "this" {
                return Err(IRError::IllegalArgumentName(arg_name.clone()));
            }
            if body_scope.symbols.contains_key(arg_name) {
                return Err(IRError::DuplicateArgumentName(arg_name.clone()));
            }
            self.symbol_table.insert(Symbol::Variable(*arg_t));
        }

        let body_id = self.symbol_table.insert(Symbol::Scope(body_scope));
        let func_symb = Symbol::Function(func_type, body_id);

        Ok((self.symbol_table.insert(func_symb), body_id))
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

    fn peek_scope(&self) -> Result<&Scope, IRError> {
        self.peek()
            .ok_or(IRError::UnscopedAccess)?
            .get_as_scope(&self.symbol_table)
            .map_err(|i| IRError::BuiltinError(BuiltinIRError::IllegalSymbolInScopeStack(i)))
    }

    fn peek_scope_mut(&mut self) -> Result<&mut Scope, IRError> {
        self.peek()
            .ok_or(IRError::UnscopedAccess)?
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
            Symbol::Variable(t) => *t,
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

        let irstmt = self.construct_ir_statement(stmt)?;
        Ok(IRNode {
            value: Box::new(IRStatement::Action(irstmt.value, IRAction::DiscardIt)),

            // FIXME: This is wrong, i'm lazy
            expr_type: TypeResolution::Unresolved,
        })
    }

    pub fn construct_ir_action_use_on_it(
        &mut self,
        stmt: Statement,
        func: IdentifierToken,
        args: Vec<Expression>,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let irstmt = self.construct_ir_statement(stmt)?;

        // FIXME: Find actual function
        let func_id = SymbolId(usize::MAX);

        let mut irargs = Vec::new();
        for arg in args {
            irargs.push(*self.construct_ir_expression(arg)?.value);
        }
        // TODO: Check that arguments are valid (count + types)

        Ok(IRNode {
            value: Box::new(IRStatement::Action(
                irstmt.value,
                IRAction::UseOnIt(func, func_id, irargs),
            )),
            // FIXME: This is wrong, i'm lazy
            expr_type: TypeResolution::Unresolved,
        })
    }

    pub fn construct_ir_action_call_it(
        &mut self,
        stmt: Statement,
        name: IdentifierToken,
    ) -> Result<IRNode<IRStatement>, IRError> {
        let irstmt = self.construct_ir_statement(stmt)?;

        let var_id = match self.lookup(&name.value) {
            Ok(i) => {
                // TODO: check if it's a variable, and if it has the right type
                i
            }
            Err(_) => {
                let var_id = self
                    .symbol_table
                    .insert(Symbol::Variable(match irstmt.expr_type {
                        TypeResolution::Unresolved => {
                            return Err(IRError::TypeShouldBeResolved(irstmt.expr_type));
                        }
                        TypeResolution::Resolved(t) => t,
                    }));
                let scope = self.peek_scope_mut()?;
                scope.symbols.insert(name.value.clone(), var_id);
                var_id
            }
        };

        Ok(IRNode {
            value: Box::new(IRStatement::Action(
                irstmt.value,
                IRAction::CallIt(name, var_id),
            )),
            expr_type: irstmt.expr_type,
        })
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
            Symbol::Function(f, _) => f,
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

        let (func_id, body_id) = self.unchecked_define_function(FunctionType {
            param_this: None,
            args: Vec::new(),
            return_type: self.builtins.void_t,
        })?;

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
