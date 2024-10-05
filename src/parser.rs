use chumsky::{prelude::*, stream::Stream};

mod expression;
pub use expression::Expr;

mod lexer;
pub use lexer::Token;

mod error;
pub use error::Error as ParseError;

mod instruction;
pub use instruction::Instruction;

pub type Span = std::ops::Range<usize>;
pub type Spanned<T> = (T, Span);

macro_rules! Parser {
    ($i:ty, $o:ty) => { impl Parser<$i, $o, Error = Simple<$i>> + Clone };
    ($i:ty, $o:ty, $lt:lifetime) => { impl Parser<$i, $o, Error = Simple<$i>> + Clone + $lt };
}
use Parser;

#[derive(Debug)]
pub enum Data {
    String(String),
    Number(Expr),
}

#[derive(Debug)]
pub struct InstructionNode {
    pub name: Spanned<String>,
    pub args: Spanned<Vec<Spanned<Token>>>,
}

#[derive(Debug)]
pub struct DirectiveNode {
    pub name: Spanned<String>,
    pub args: Spanned<Vec<Spanned<Data>>>,
}

#[derive(Debug)]
pub enum Statement {
    Directive(DirectiveNode),
    Instruction(InstructionNode),
}

#[derive(Debug)]
pub struct ASTNode {
    pub labels: Vec<Spanned<String>>,
    pub statement: Spanned<Statement>,
}

#[must_use]
fn parser<'a>() -> Parser!(Token, Vec<ASTNode>, 'a) {
    // Newline token
    let newline = || just(Token::Ctrl('\n'));
    // Identifiers
    let ident = select! {|span| Token::Identifier(ident) => (ident, span)}.labelled("identifier");
    let label = select! {|span| Token::Label(name) => (name, span)}
        .padded_by(newline().repeated())
        .labelled("label");
    let directive =
        select! {|span| Token::Directive(name) => (name, span)}.labelled("directive name");

    // Any amount of labels: `labels -> label*`
    let labels = label.repeated().collect().labelled("labels");

    // Directive statement `directive_statement -> directive expression (\n*,\n* expression)*\n`
    let directive_statement = directive
        .then(
            // Arguments of the directive. Comma-separated list of expressions. Each expression can
            // have any amount of newlines prefixing it, and any amount of newlines following it if
            // they are followed by a comma (indicating that more expressions will follow,
            // otherwise the first newline is used as the statement end)
            newline()
                .repeated()
                .ignore_then(
                    expression::parser()
                        .map(Data::Number)
                        .or(select! {Token::String(s) => Data::String(s)})
                        .map_with_span(|x, span| (x, span)),
                )
                .then_ignore(
                    newline()
                        .repeated()
                        .then(just(Token::Ctrl(',')).rewind())
                        .or_not(),
                )
                .separated_by(just(Token::Ctrl(',')))
                .map_with_span(|x, span| (x, span))
                .labelled("parameters"),
        )
        .then_ignore(newline())
        .map(|(name, args)| Statement::Directive(DirectiveNode { name, args }))
        .labelled("data directive");

    // Instruction: `instruction -> ident [^\n]*`
    let instruction = ident
        .then(
            newline()
                .not()
                .map_with_span(|token, span| (token, span))
                .repeated()
                .map_with_span(|args, span| (args, span)),
        )
        .map(|(name, args)| Statement::Instruction(InstructionNode { name, args }))
        .labelled("instruction");

    // Statement: `statement -> labels [instruction | directive_statement]`
    let statement = labels
        .then(
            directive_statement
                .or(instruction)
                .map_with_span(|x, s| (x, s)),
        )
        .padded_by(newline().repeated())
        .map(|(labels, statement)| ASTNode { labels, statement });

    statement.repeated().then_ignore(end())
}

fn parse_with<T>(parser: Parser!(Token, T), src: &str) -> Result<T, ParseError> {
    let tokens = lexer::lexer().parse(src)?;
    let len = src.chars().count();
    #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
    let stream = Stream::from_iter(len..len + 1, tokens.into_iter());
    Ok(parser.parse(stream)?)
}

pub fn parse(src: &str) -> Result<Vec<ASTNode>, ParseError> {
    parse_with(parser(), src)
}

#[derive(Debug, Clone)]
pub enum Argument {
    Identifier(String),
    Number(Expr),
}
