use crate::lang::{token::IdentifierToken, types::SymbolId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeResolution {
    Resolved(SymbolId),
    Unresolved,
}

impl TypeResolution {
    pub fn type_id_now(&self) -> Option<SymbolId> {
        match self {
            TypeResolution::Resolved(t) => Some(*t),
            TypeResolution::Unresolved => None,
        }
    }

    pub fn type_id_now_or_err(&self) -> Result<SymbolId, IRError> {
        self.type_id_now()
            .ok_or_else(|| IRError::TypeShouldBeResolved(*self))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IRNode<T> {
    pub value: Box<T>,
    pub expr_type: TypeResolution,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinIRError {
    IllegalSymbolInScopeStack(SymbolId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRError {
    TypeMismatch(TypeResolution, TypeResolution), // Expected, Actual
    MultipleMainFunctionDeclarations(SymbolId),
    ReferedSymbolIsNotCallable(SymbolId),
    ReferedSymbolIsNotVariable(SymbolId),
    TypeShouldBeResolved(TypeResolution),
    InvalidReferableSymbol(SymbolId),
    InvalidFunctionSymbol(SymbolId),
    IllegalAccess(String, SymbolId),
    DuplicateArgumentName(String),
    DuplicateFunctionName(String),
    BuiltinError(BuiltinIRError),
    IllegalArgumentName(String),
    UnknownIdentifier(String),
    InvalidSymbolId(SymbolId),
    IllegalUnnamedArgument,
    InvalidDiscardAction,
    UnscopedAccess,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRExpression {
    IntI64(i64),
    Identifier(IdentifierToken, SymbolId),
    Call(Option<IdentifierToken>, SymbolId, Vec<IRExpression>), // function name, function id, arguments
    Block(Vec<IRStatement>, SymbolId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRAction {
    ReturnIt,
    DiscardIt,
    UseOnIt(IdentifierToken, SymbolId, Vec<IRExpression>), // function name, function id, arguments
    CallIt(IdentifierToken, SymbolId),                     // variable name, variable id
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IRWhileLoop {
    pub condition: Box<IRExpression>,
    pub body: Box<IRExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IRElseIfPart {
    pub condition: IRExpression,
    pub body: IRExpression,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IRIfStatement {
    pub if_condition: Box<IRExpression>,
    pub if_body: Box<IRExpression>,
    pub else_ifs: Vec<IRElseIfPart>,
    pub else_body: Option<Box<IRExpression>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IRActions {
    pub statement: Box<IRStatement>,
    pub actions: Vec<IRAction>,
    pub type_stack: Vec<SymbolId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRStatement {
    VoidDeclaration(Box<IRDeclaration>),
    Take(IRExpression),
    Actions(IRActions),
    WhileLoop(IRWhileLoop),
    IfStatement(IRIfStatement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IRTypeMainFunction {
    pub func_id: SymbolId,
    pub body_scope_id: SymbolId,
    pub body: Box<IRExpression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRDeclaration {
    MainFunction(Box<IRTypeMainFunction>),
}
