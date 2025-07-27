use crate::lang::{
    ast::{
        Action, BooleanOperator, ComparisonOperator, Declaration, DoType, Expression,
        MainFunctionDeclaration, Statement,
    },
    token::{IdentifierToken, Token},
};

pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

#[derive(Debug, Clone)]
pub struct SuccessParse<T> {
    pub result: T,
    pub pos_range: (usize, usize),
    pub caps_count: usize,
    pub total_letters: usize,
    pub politeness: i32,
}

fn count_politeness(value: &str) -> i32 {
    if value.eq_ignore_ascii_case("please") {
        1
    } else if value.eq_ignore_ascii_case("fuck") {
        -2
    } else {
        0
    }
}

impl<T> SuccessParse<T> {
    pub fn combine<U>(self, other: SuccessParse<U>) -> SuccessParse<(T, U)> {
        SuccessParse {
            result: (self.result, other.result),
            pos_range: (
                self.pos_range.0.min(other.pos_range.0),
                self.pos_range.1.max(other.pos_range.1),
            ),
            caps_count: self.caps_count + other.caps_count,
            total_letters: self.total_letters + other.total_letters,
            politeness: self.politeness + other.politeness,
        }
    }

    pub fn maybe_combine<U>(
        self,
        f: impl FnOnce() -> ParseResult<U>,
    ) -> SuccessParse<(T, Option<U>)> {
        match f() {
            Ok(other) => self.and_then(other, |(v, u)| (v, Some(u))),
            Err(_) => self.map(|v| (v, None)),
        }
    }

    pub fn ignore_but_combine<U>(self, other: SuccessParse<U>) -> SuccessParse<U> {
        self.combine(other).map(|(_, v)| v)
    }

    pub fn combine_but_ignore<U>(self, other: SuccessParse<U>) -> SuccessParse<T> {
        self.combine(other).map(|(v, _)| v)
    }

    pub fn and_then<U, O, F>(self, other: SuccessParse<U>, f: F) -> SuccessParse<O>
    where
        F: FnOnce((T, U)) -> O,
    {
        self.combine(other).map(f)
    }

    pub fn map<O, F>(self, f: F) -> SuccessParse<O>
    where
        F: FnOnce(T) -> O,
    {
        SuccessParse {
            result: f(self.result),
            pos_range: self.pos_range,
            caps_count: self.caps_count,
            total_letters: self.total_letters,
            politeness: self.politeness,
        }
    }

    pub fn try_map<O, F>(self, f: F) -> Option<SuccessParse<O>>
    where
        F: FnOnce(T) -> Option<O>,
    {
        f(self.result).map(|result| SuccessParse {
            result,
            pos_range: self.pos_range,
            caps_count: self.caps_count,
            total_letters: self.total_letters,
            politeness: self.politeness,
        })
    }

    pub fn try_map_err<O, F, E>(self, f: F) -> Result<SuccessParse<O>, E>
    where
        F: FnOnce(T) -> Result<O, E>,
    {
        f(self.result).map(|result| SuccessParse {
            result,
            pos_range: self.pos_range,
            caps_count: self.caps_count,
            total_letters: self.total_letters,
            politeness: self.politeness,
        })
    }

    pub fn ignore(self) -> SuccessParse<()> {
        self.map(|_| ())
    }

    pub fn increase_politeness(self, value: i32) -> SuccessParse<T> {
        SuccessParse {
            result: self.result,
            pos_range: self.pos_range,
            caps_count: self.caps_count,
            total_letters: self.total_letters,
            politeness: self.politeness + value,
        }
    }
}

#[derive(Debug)]
pub enum ParseError {
    Many(Vec<ParseError>),
    UnexpectedToken(usize),
    UnexpectedEOF,
    InvalidInteger,
}

pub type ParseResult<T> = Result<SuccessParse<T>, ParseError>;

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn advance(&mut self) {
        self.position += 1;
    }

    fn try_to<O>(&mut self, f: impl FnOnce(&mut Self) -> ParseResult<O>) -> ParseResult<O> {
        let position = self.position;
        let result = f(self);
        if result.is_err() {
            self.position = position;
        }
        result
    }

    fn try_first_of<O>(&mut self, f: &[fn(&mut Self) -> ParseResult<O>]) -> ParseResult<O> {
        let position = self.position;
        let mut errs = Vec::new();
        for f in f {
            match self.try_to(f) {
                Ok(v) => return Ok(v),
                Err(e) => {
                    self.position = position;
                    errs.push(e);
                }
            }
        }
        Err(ParseError::Many(errs))
    }

    fn expect_identifier(&mut self) -> ParseResult<IdentifierToken> {
        match self.peek() {
            Some(Token::Identifier(idt)) => {
                let idt = idt.clone();
                let position = self.position;
                self.advance();
                Ok(SuccessParse {
                    caps_count: idt.value.chars().filter(|c| c.is_uppercase()).count(),
                    total_letters: idt.value.chars().filter(|c| c.is_alphabetic()).count(),
                    pos_range: (position, position),
                    result: idt,
                    politeness: 0,
                })
            }
            _ => Err(ParseError::UnexpectedToken(self.position)),
        }
    }

    fn expect_lang_piece(&mut self, value: &str) -> ParseResult<IdentifierToken> {
        match self.peek() {
            Some(Token::Identifier(lpt)) => {
                if lpt.value.eq_ignore_ascii_case(value) {
                    let lpt = lpt.clone();
                    let position = self.position;
                    self.advance();
                    Ok(SuccessParse {
                        caps_count: lpt.value.chars().filter(|c| c.is_uppercase()).count(),
                        total_letters: lpt.value.chars().filter(|c| c.is_alphabetic()).count(),
                        pos_range: (position, position),
                        politeness: count_politeness(&lpt.value),
                        result: lpt,
                    })
                } else {
                    Err(ParseError::UnexpectedToken(self.position))
                }
            }
            _ => Err(ParseError::UnexpectedToken(self.position)),
        }
    }

    fn parse_block_expression(&mut self) -> ParseResult<Expression> {
        Ok(self
            .expect_lang_piece("{")?
            .ignore_but_combine(self.parse_block()?)
            .combine_but_ignore(self.expect_lang_piece("}")?))
    }

    fn parse_boolean_base(&mut self) -> ParseResult<Expression> {
        if let Ok(v) = self.try_to(|p| p.expect_lang_piece("not")) {
            Ok(v.ignore_but_combine(self.try_first_of(&[
                |p| p.parse_expression_comp(),
                |p| {
                    Ok(p.expect_lang_piece("(")?
                        .ignore_but_combine(p.parse_boolean_expression()?)
                        .combine_but_ignore(p.expect_lang_piece(")")?))
                },
            ])?)
            .map(|v| Expression::BooleanNegate(Box::new(v))))
        } else {
            self.try_first_of(&[
                |p| p.parse_expression_comp(),
                |p| {
                    Ok(p.expect_lang_piece("this")?
                        .ignore_but_combine(p.expect_lang_piece(":")?)
                        .ignore_but_combine(p.expect_lang_piece("(")?)
                        .ignore_but_combine(p.parse_boolean_expression()?)
                        .combine_but_ignore(p.expect_lang_piece(")")?))
                },
            ])
        }
    }

    fn parse_boolean_operator(&mut self) -> ParseResult<BooleanOperator> {
        self.try_first_of(&[
            |p| Ok(p.expect_lang_piece("and")?.map(|_| BooleanOperator::And)),
            |p| Ok(p.expect_lang_piece("or")?.map(|_| BooleanOperator::Or)),
            |p| Ok(p.expect_lang_piece("xor")?.map(|_| BooleanOperator::Xor)),
            |p| {
                Ok(p.expect_lang_piece("eclusive")?
                    .combine(p.expect_lang_piece("or")?)
                    .map(|_| BooleanOperator::Xor))
            },
            |p| {
                Ok(p.expect_lang_piece("implies")?
                    .map(|_| BooleanOperator::Implies))
            },
            |p| Ok(p.expect_lang_piece("nand")?.map(|_| BooleanOperator::Nand)),
            |p| {
                Ok(p.expect_lang_piece("negated")?
                    .combine(p.expect_lang_piece("and")?)
                    .map(|_| BooleanOperator::Nand))
            },
            |p| Ok(p.expect_lang_piece("nor")?.map(|_| BooleanOperator::Nor)),
            |p| {
                Ok(p.expect_lang_piece("negated")?
                    .combine(p.expect_lang_piece("or")?)
                    .map(|_| BooleanOperator::Nor))
            },
            |p| Ok(p.expect_lang_piece("xnor")?.map(|_| BooleanOperator::Xnor)),
            |p| {
                Ok(p.expect_lang_piece("exclusive")?
                    .combine(p.expect_lang_piece("nor")?)
                    .map(|_| BooleanOperator::Xnor))
            },
            |p| {
                Ok(p.expect_lang_piece("negated")?
                    .combine(p.expect_lang_piece("xor")?)
                    .map(|_| BooleanOperator::Xnor))
            },
            |p| {
                Ok(p.expect_lang_piece("negated")?
                    .combine(p.expect_lang_piece("exclusive")?)
                    .combine(p.expect_lang_piece("or")?)
                    .map(|_| BooleanOperator::Xnor))
            },
            |p| {
                Ok(p.expect_lang_piece("is")?
                    .combine(p.expect_lang_piece("implied")?)
                    .combine(p.expect_lang_piece("by")?)
                    .map(|_| BooleanOperator::ImpliedBy))
            },
        ])
    }

    fn parse_boolean_expression(&mut self) -> ParseResult<Expression> {
        let base = self.parse_boolean_base()?;

        match self.try_to(|p| p.parse_boolean_operator()) {
            Ok(v) => Ok(base
                .combine(v)
                .and_then(self.parse_boolean_base()?, |((e1, op), e2)| {
                    Expression::Boolean(Box::new(e1), op, Box::new(e2))
                })),
            Err(_) => Ok(base),
        }
    }

    fn parse_comparison_operator(&mut self) -> ParseResult<ComparisonOperator> {
        self.try_first_of(&[
            |p| {
                Ok(p.expect_lang_piece("equals")?
                    .map(|_| ComparisonOperator::Equals))
            },
            |p| {
                Ok(p.expect_lang_piece("is")?
                    .combine(p.expect_lang_piece("equal")?)
                    .combine(p.expect_lang_piece("to")?)
                    .map(|_| ComparisonOperator::Equals))
            },
            |p| {
                Ok(p.expect_lang_piece("does")?
                    .combine(p.expect_lang_piece("not")?)
                    .combine(p.expect_lang_piece("equal")?)
                    .combine(p.expect_lang_piece("to")?)
                    .map(|_| ComparisonOperator::NotEquals))
            },
            |p| {
                Ok(p.expect_lang_piece("is")?
                    .combine(p.expect_lang_piece("greater")?)
                    .combine(p.expect_lang_piece("than")?)
                    .map(|_| ComparisonOperator::GreaterThan))
            },
            |p| {
                Ok(p.expect_lang_piece("is")?
                    .combine(p.expect_lang_piece("less")?)
                    .combine(p.expect_lang_piece("than")?)
                    .map(|_| ComparisonOperator::LessThan))
            },
            |p| {
                Ok(p.expect_lang_piece("is")?
                    .combine(p.expect_lang_piece("greater")?)
                    .combine(p.expect_lang_piece("than")?)
                    .combine(p.expect_lang_piece("or")?)
                    .combine(p.expect_lang_piece("equal")?)
                    .combine(p.expect_lang_piece("to")?)
                    .map(|_| ComparisonOperator::GreaterThanOrEqual))
            },
            |p| {
                Ok(p.expect_lang_piece("is")?
                    .combine(p.expect_lang_piece("less")?)
                    .combine(p.expect_lang_piece("than")?)
                    .combine(p.expect_lang_piece("or")?)
                    .combine(p.expect_lang_piece("equal")?)
                    .combine(p.expect_lang_piece("to")?)
                    .map(|_| ComparisonOperator::LessThanOrEqual))
            },
        ])
    }

    fn parse_expression_comp(&mut self) -> ParseResult<Expression> {
        let base = self.parse_expression()?;

        match self.try_to(|p| p.parse_comparison_operator()) {
            Ok(v) => Ok(base
                .combine(v)
                .and_then(self.parse_expression()?, |((e1, op), e2)| {
                    Expression::Comparison(Box::new(e1), op, Box::new(e2))
                })),
            Err(_) => Ok(base),
        }
    }

    fn parse_expression(&mut self) -> ParseResult<Expression> {
        let mut errs = Vec::new();

        match self.try_to(|p| p.expect_identifier()) {
            Ok(v) => return Ok(v.map(|idt| Expression::Identifier(idt))),
            Err(e) => {
                errs.push(e);
            }
        }

        match self.try_to(|p| p.parse_block_expression()) {
            Ok(v) => return Ok(v),
            Err(e) => {
                errs.push(e);
            }
        }

        match self.peek() {
            Some(Token::IntegerLiteral(int_tok)) => {
                let int_tok = int_tok.clone();
                let position = self.position;
                self.advance();
                return Ok(SuccessParse {
                    caps_count: 0,
                    total_letters: int_tok.value.chars().filter(|c| c.is_alphabetic()).count(),
                    pos_range: (position, position),
                    politeness: count_politeness(&int_tok.value),
                    result: Expression::IntI64(int_tok.value.parse().unwrap()),
                });
            }
            _ => {
                errs.push(ParseError::UnexpectedToken(self.position));
            }
        }

        Err(ParseError::Many(errs))
    }

    fn parse_fncall_args(&mut self) -> ParseResult<Vec<Expression>> {
        let mut args = self.try_to(|p| p.parse_expression())?.map(|arg| vec![arg]);

        while self.try_to(|p| p.expect_lang_piece(",")).is_ok() {
            let arg = self.try_to(|p| p.parse_expression())?;
            args = args.and_then(arg, |(mut v, arg)| {
                v.push(arg);
                v
            });
        }

        if self.try_to(|p| p.expect_lang_piece("and")).is_ok() {
            let arg = self.try_to(|p| p.parse_expression())?;
            args = args.and_then(arg, |(mut v, arg)| {
                v.push(arg);
                v
            });
        } else if args.result.len() > 1 {
            return Err(ParseError::UnexpectedToken(self.position));
        }

        Ok(args)
    }

    fn parse_function_call(&mut self) -> ParseResult<Statement> {
        Ok(self
            .expect_lang_piece("I")?
            .combine(self.try_first_of(&[
                |p| {
                    Ok(p.expect_lang_piece("want")?
                        .ignore()
                        .increase_politeness(-1))
                },
                |p| {
                    Ok(p.expect_lang_piece("would")?
                        .combine(p.try_first_of(&[
                            |p| Ok(p.expect_lang_piece("like")?),
                            |p| Ok(p.expect_lang_piece("love")?.increase_politeness(1)),
                        ])?)
                        .ignore())
                },
            ])?)
            .combine(self.expect_lang_piece("to")?)
            .ignore_but_combine(self.expect_identifier()?)
            .combine(self.parse_fncall_args()?)
            .map(|(idt, args)| Statement::Call(idt, args)))
    }

    fn parse_take_statement(&mut self) -> ParseResult<Statement> {
        Ok(self
            .expect_lang_piece("take")?
            .ignore_but_combine(self.parse_expression()?)
            .map(|expr| Statement::Take(Box::new(expr))))
    }

    fn parse_do_unless(&mut self) -> ParseResult<DoType> {
        Ok(self
            .expect_lang_piece("unless")?
            .ignore_but_combine(self.parse_boolean_expression()?)
            .map(|expr| DoType::Unless(Box::new(expr))))
    }

    fn parse_do_until(&mut self) -> ParseResult<DoType> {
        Ok(self
            .expect_lang_piece("until")?
            .ignore_but_combine(self.parse_boolean_expression()?)
            .map(|expr| DoType::Until(Box::new(expr))))
    }

    fn parse_do_type(&mut self) -> ParseResult<DoType> {
        self.try_first_of(&[|p| p.parse_do_unless(), |p| p.parse_do_until()])
    }

    fn parse_do_statement(&mut self) -> ParseResult<Statement> {
        Ok(self
            .expect_lang_piece("do")?
            .ignore_but_combine(self.parse_block_expression()?)
            .and_then(self.parse_do_type()?, |(expr, do_type)| {
                Statement::Do(Box::new(expr), do_type)
            }))
    }

    fn parse_statement_base(&mut self) -> ParseResult<Statement> {
        self.try_first_of(&[
            |p| p.parse_function_call(),
            |p| p.parse_take_statement(),
            |p| p.parse_do_statement(),
        ])
    }

    fn parse_action_call_it(&mut self) -> ParseResult<Action> {
        Ok(self
            .expect_lang_piece("call")?
            .combine(self.expect_lang_piece("it")?)
            .ignore_but_combine(self.expect_identifier()?)
            .map(|idt| Action::CallIt(idt)))
    }

    fn parse_action_return_it(&mut self) -> ParseResult<Action> {
        Ok(self
            .expect_lang_piece("return")?
            .combine(self.expect_lang_piece("it")?)
            .map(|_| Action::ReturnIt))
    }

    fn parse_action_use_on_it(&mut self) -> ParseResult<Action> {
        Ok(self
            .expect_lang_piece("use")?
            .ignore_but_combine(self.expect_identifier()?)
            .combine_but_ignore(self.expect_lang_piece("on")?)
            .combine_but_ignore(self.expect_lang_piece("it")?)
            .maybe_combine(|| {
                self.try_to(|p| {
                    Ok(p.expect_lang_piece("with")?
                        .ignore_but_combine(p.try_first_of(&[
                            |p| {
                                Ok(p.expect_lang_piece("just")?
                                    .ignore_but_combine(p.parse_expression()?)
                                    .map(|expr| vec![expr]))
                            },
                            |p| {
                                let args = p.parse_fncall_args()?;
                                if args.result.is_empty() {
                                    Err(ParseError::UnexpectedToken(args.pos_range.0))
                                } else {
                                    Ok(args)
                                }
                            },
                        ])?))
                })
            })
            .map(|(idt, args)| Action::UseOnIt(idt, args.unwrap_or_else(|| Vec::new()))))
    }

    fn parse_action_discard_it(&mut self) -> ParseResult<Action> {
        Ok(self
            .expect_lang_piece("discard")?
            .combine(self.expect_lang_piece("it")?)
            .map(|_| Action::DiscardIt))
    }

    fn parse_action(&mut self) -> ParseResult<Action> {
        self.try_first_of(&[
            |p| p.parse_action_call_it(),
            |p| p.parse_action_return_it(),
            |p| p.parse_action_use_on_it(),
            |p| p.parse_action_discard_it(),
        ])
    }

    fn parse_statement(&mut self) -> ParseResult<Statement> {
        let mut statement = self.parse_statement_base()?;

        while self.try_to(|p| p.expect_lang_piece(",")).is_ok() {
            self.expect_lang_piece("then")?;
            statement = statement.and_then(self.parse_action()?, |(s, a)| {
                Statement::Action(Box::new(s), a)
            });
        }

        self.expect_lang_piece(".")?;

        Ok(statement)
    }

    fn parse_block(&mut self) -> ParseResult<Expression> {
        let mut res = SuccessParse {
            result: Vec::new(),
            pos_range: (self.position, self.position),
            caps_count: 0,
            total_letters: 0,
            politeness: 0,
        };

        loop {
            match self.try_to(|p| p.parse_statement()) {
                Ok(p) => {
                    res = res.and_then(p, |(mut v, e)| {
                        v.push(e);
                        v
                    })
                }
                Err(_) => break,
            }
        }

        Ok(res.map(|v| Expression::Block(v)))
    }

    fn parse_greet(&mut self) -> ParseResult<()> {
        const GREETS: [(&[&str], i32); 16] = [
            (&["hello"], 1),
            (&["hi"], 1),
            (&["hey"], 1),
            (&["yo"], 2),
            (&["greeting"], 2),
            (&["greetings"], 4),
            (&["hiya"], 1),
            (&["bitch"], -4),
            (&["mf"], -2),
            (&["dumb"], -1),
            (&["dumbass"], -1),
            (&["fucking"], -5),
            (&["listen", "up", "stupid"], -10),
            (&["hey", "you", "dumbass"], -8),
            (&["yoooo", "mister"], 7),
            (&["listen", "up", "you", "fucking", "useless"], -25), // this hurts the compiler's feelings
        ];

        for (greet, politeness) in GREETS {
            if let Ok(v) = self.try_to(|p| {
                let mut res = p.expect_lang_piece(greet[0])?.ignore();
                for g in greet.iter().skip(1) {
                    res = res.combine(p.expect_lang_piece(g)?).ignore();
                }
                Ok(res)
            }) {
                return Ok(v.increase_politeness(politeness));
            }
        }

        Err(ParseError::UnexpectedToken(self.position))
    }

    fn parse_compiler_greet(&mut self) -> ParseResult<()> {
        Ok(self
            .parse_greet()?
            .combine(self.expect_lang_piece("compiler")?)
            .ignore())
    }

    fn parse_descriptor(&mut self) -> ParseResult<()> {
        const DESCRIPTORS: [(&str, i32); 13] = [
            ("fucking", -5),
            ("dumb", -1),
            ("dumbass", -3),
            ("stupid", -1),
            ("stupidass", -4),
            ("idiot", -1),
            ("idiotass", -3),
            ("ass", -2),
            ("asshole", -5),
            ("mf", -4),
            ("cool", 2),
            ("coolaf", 5),
            ("shit", -3),
        ];

        for (desc, politeness) in DESCRIPTORS {
            if let Ok(v) = self.try_to(|p| p.expect_lang_piece(desc)) {
                return Ok(v.ignore().increase_politeness(politeness));
            }
        }

        Err(ParseError::UnexpectedToken(self.position))
    }

    pub fn parse_main_function_declaration(&mut self) -> ParseResult<Declaration> {
        Ok(self
            .parse_compiler_greet()?
            .combine(self.expect_lang_piece(",")?)
            .combine(self.expect_lang_piece("the")?)
            .maybe_combine(|| self.try_to(|p| p.parse_descriptor()))
            .combine(self.expect_lang_piece("program")?)
            .combine(self.expect_lang_piece("starts")?)
            .combine(self.expect_lang_piece("here")?)
            .combine(self.expect_lang_piece(".")?)
            .ignore_but_combine(self.parse_block()?)
            .and_then(
                self.expect_lang_piece("done")?
                    .combine(self.expect_lang_piece(".")?),
                |(blk, _)| Declaration::MainFunction(MainFunctionDeclaration { body: blk }),
            ))
    }
}
