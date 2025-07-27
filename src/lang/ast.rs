use crate::lang::token::IdentifierToken;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    IntI64(i64),
    Block(Vec<Statement>),
    Identifier(IdentifierToken),
    Comparison(Box<Expression>, ComparisonOperator, Box<Expression>),
    Boolean(Box<Expression>, BooleanOperator, Box<Expression>),
    BooleanNegate(Box<Expression>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComparisonOperator {
    Equals,
    NotEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BooleanOperator {
    And,
    Or,
    Xor,
    Nand,
    Nor,
    Xnor,
    Implies,
    ImpliedBy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    CallIt(IdentifierToken),
    UseOnIt(IdentifierToken, Vec<Expression>),
    ReturnIt,
    DiscardIt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DoType {
    Unless(Box<Expression>),
    Until(Box<Expression>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    VoidDeclaration(Box<Declaration>),
    Call(IdentifierToken, Vec<Expression>),
    Action(Box<Statement>, Action),
    Do(Box<Expression>, DoType),
    Take(Box<Expression>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declaration {
    MainFunction(MainFunctionDeclaration),
    Variable(VarDeclaration),
    Function(FunctionDeclaration),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDeclaration {
    pub name: String,
    pub value: Option<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDeclaration {
    pub name: String,
    pub params: Vec<String>,
    pub body: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MainFunctionDeclaration {
    pub body: Expression,
}
