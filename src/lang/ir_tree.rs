use crate::lang::{
    ast::{BooleanOperator, ComparisonOperator},
    token::IdentifierToken,
    types::SymbolId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeResolution {
    Resolved(SymbolId),
    Unresolved,
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
    MultipleMainFunctionDeclarations(SymbolId),
    ReferedSymbolIsNotCallable(SymbolId),
    TypeShouldBeResolved(TypeResolution),
    InvalidReferableSymbol(SymbolId),
    DuplicateArgumentName(String),
    BuiltinError(BuiltinIRError),
    IllegalArgumentName(String),
    UnknownIdentifier(String),
    InvalidSymbolId(SymbolId),
    TypeMismatch(TypeResolution, TypeResolution), // Expected, Actual
    InvalidDiscardAction,
    UnscopedAccess,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRExpression {
    IntI64(i64),
    Identifier(IdentifierToken, SymbolId),
    Call(IdentifierToken, SymbolId, Vec<IRExpression>), // function name, function id, arguments
    Comparison(Box<IRExpression>, ComparisonOperator, Box<IRExpression>),
    BooleanOp(Box<IRExpression>, BooleanOperator, Box<IRExpression>),
    BooleanNegate(Box<IRExpression>),
    Block(Vec<IRStatement>),
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
pub enum IRStatement {
    VoidDeclaration(Box<IRDeclaration>),
    Take(IRExpression),
    Action(Box<IRStatement>, IRAction),

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
