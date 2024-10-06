use chumsky::{prelude::*, stream::Stream};

mod expression;
pub use expression::Expr;

mod lexer;
pub use lexer::Token;

mod error;
pub use error::Error as ParseError;

mod instruction;
pub use instruction::{Argument, Instruction};

/// Range of characters in the source code of an element
pub type Span = std::ops::Range<usize>;
/// Value with an attached `Span`
pub type Spanned<T> = (T, Span);

/// Generic parser type definition
macro_rules! Parser {
    ($i:ty, $o:ty) => { impl Parser<$i, $o, Error = Simple<$i>> + Clone };
    ($i:ty, $o:ty, $lt:lifetime) => { impl Parser<$i, $o, Error = Simple<$i>> + Clone + $lt };
}
use Parser;

/// AST node for directive arguments
#[derive(Debug)]
pub enum Data {
    /// String literal
    String(String),
    /// Numeric expression
    Number(Expr),
}

/// AST node for instructions
#[derive(Debug)]
pub struct InstructionNode {
    /// Name of the instruction
    pub name: Spanned<String>,
    /// Arguments of the instruction, to be checked/used on the semantic stage
    pub args: Spanned<Vec<Spanned<Token>>>,
}

/// AST node for directives
#[derive(Debug)]
pub struct DirectiveNode {
    /// Name of the directive
    pub name: Spanned<String>,
    /// Arguments of the directive
    pub args: Spanned<Vec<Spanned<Data>>>,
}

/// AST node for statements
#[derive(Debug)]
pub enum Statement {
    Directive(DirectiveNode),
    Instruction(InstructionNode),
}

/// Top level AST node
#[derive(Debug)]
pub struct ASTNode {
    /// Labels attached to the node
    pub labels: Vec<Spanned<String>>,
    /// Statement of the node
    pub statement: Spanned<Statement>,
}

/// Creates a parser for the tokenized input
#[must_use]
fn parser<'a>() -> Parser!(Token, Vec<ASTNode>, 'a) {
    // Newline token
    let newline = || just(Token::Ctrl('\n'));
    // Identifiers
    let ident = select! {|span| Token::Identifier(ident) => (ident, span)}.labelled("identifier");
    let label = select! {|span| Token::Label(name) => (name, span)}
        .padded_by(newline().repeated())
        .labelled("label");
    let directive_name =
        select! {|span| Token::Directive(name) => (name, span)}.labelled("directive name");

    // Any amount of labels: `labels -> label*`
    let labels = label.repeated().collect().labelled("labels");

    // Directive statement:
    // `directive -> (directive_name \n)
    //             | (directive_name \n* expression (\n* , \n* expression)* \n)`
    let directive = directive_name
        .then(
            // Arguments of the directive. Comma-separated list of expressions. Each expression can
            // have any amount of newlines prefixing it, and any amount of newlines following it if
            // they are followed by a comma (indicating that more expressions will follow,
            // otherwise a single newline is required as the statement end)
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

    // Statement: `statement -> labels [instruction | directive]`
    let statement = labels
        .then(directive.or(instruction).map_with_span(|x, s| (x, s)))
        .padded_by(newline().repeated())
        .map(|(labels, statement)| ASTNode { labels, statement });

    // `code -> statement*`
    statement.repeated().then_ignore(end())
}

/// Tokenizes an input and parses it with a given parser
///
/// # Parameters
///
/// * `parser`: parser to use with the tokenized input
/// * `src`: code to tokenize and parse
///
/// # Errors
///
/// Errors if the input either has an invalid token or it's syntactically invalid according to the
/// given parser
fn parse_with<T>(parser: Parser!(Token, T), src: &str) -> Result<T, ParseError> {
    let tokens = lexer::lexer().parse(src)?; // Tokenize the input
    let len = src.chars().count(); // Count the amount of chars in the input to calculate the end span
    #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
    let stream = Stream::from_iter(len..len + 1, tokens.into_iter());
    Ok(parser.parse(stream)?)
}

/// Parses the input creating an abstract syntax tree
///
/// # Parameters
///
/// * `src`: code to parse
///
/// # Errors
///
/// Errors if the input is syntactically invalid
pub fn parse(src: &str) -> Result<Vec<ASTNode>, ParseError> {
    parse_with(parser(), src)
}
