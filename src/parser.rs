use chumsky::{prelude::*, stream::Stream};

mod expression;
pub use expression::Expr;

mod lexer;
pub use lexer::Token;

mod error;
pub use error::Error as ParseError;

mod instruction;
pub use instruction::Instruction;

use crate::architecture::{Architecture, DirectiveSegment};

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
    pub labels: Vec<Spanned<String>>,
    pub name: Spanned<String>,
    pub args: Spanned<Vec<Spanned<Token>>>,
}

#[derive(Debug)]
pub struct DataNode {
    pub labels: Vec<Spanned<String>>,
    pub name: Spanned<String>,
    pub args: Spanned<Vec<Spanned<Data>>>,
}

#[derive(Debug)]
pub enum ASTNode {
    CodeSegment(Vec<InstructionNode>),
    DataSegment(Vec<DataNode>),
}

#[must_use]
fn parser<'a>(arch: &'a Architecture) -> Parser!(Token, Vec<ASTNode>, 'a) {
    // Newline token
    let newline = || just(Token::Ctrl('\n'));
    // Identifiers
    let ident = select! {Token::Identifier(ident) => ident}.labelled("identifier");
    let label = select! {Token::Label(name) => name}
        .padded_by(newline().repeated())
        .labelled("label");
    let directive = select! {Token::Directive(name) => name}.labelled("directive name");

    // Any amount of labels: `labels -> label*`
    let labels = label
        .map_with_span(|x, span| (x, span))
        .repeated()
        .collect()
        .labelled("labels");

    // Data statement: statements within the data segment
    // `data_statement -> labels directive expression (, expression)*`
    let data_statement = labels
        .clone()
        .then(directive.map_with_span(|name, span| (name, span)))
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
                .at_least(1)
                .map_with_span(|x, span| (x, span))
                .labelled("parameters"),
        )
        .then_ignore(newline())
        .padded_by(newline().repeated())
        .map(|((labels, name), args)| DataNode { labels, name, args })
        .labelled("data directive");

    // Name of the directive changing to the data segment
    let data_segment_directive = arch.get_directive_segment(DirectiveSegment::Data);
    // Name of the directive changing to the code segment
    let code_segment_directive = arch.get_directive_segment(DirectiveSegment::Code);

    // Data segment: `data_segment -> data_segment_directive data_statement*`
    let data_segment = directive
        .then_ignore(newline())
        .try_map(move |name: String, span| {
            if name == data_segment_directive {
                Ok(())
            } else {
                Err(Simple::custom(span, "TODO: error message data"))
            }
        })
        .ignore_then(data_statement.repeated())
        .map(ASTNode::DataSegment);

    // Instruction: `instruction -> labels ident [^\n]*`
    let instruction = labels
        .then(ident.map_with_span(|name, span| (name, span)))
        .then(
            newline()
                .not()
                .map_with_span(|token, span| (token, span))
                .repeated()
                .map_with_span(|args, span| (args, span)),
        )
        .padded_by(newline().repeated())
        .map(|((labels, name), args)| InstructionNode { labels, name, args })
        .labelled("instruction");

    // Code segment: `code_segment -> code_segment_directive instruction*`
    let code_segment = directive
        .then_ignore(newline())
        .try_map(move |name: String, span| {
            if name == code_segment_directive {
                Ok(())
            } else {
                Err(Simple::custom(span, "TODO: error message code"))
            }
        })
        .ignore_then(instruction.repeated())
        .map(ASTNode::CodeSegment);

    data_segment.or(code_segment).repeated().then_ignore(end())
}

pub fn parse(arch: &Architecture, src: &str) -> Result<Vec<ASTNode>, ParseError> {
    let tokens = lexer::lexer().parse(src)?;
    let len = src.chars().count();
    #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
    let stream = Stream::from_iter(len..len + 1, tokens.into_iter());
    Ok(parser(arch).parse(stream)?)
}

#[derive(Debug, Clone)]
pub enum Argument {
    Identifier(String),
    Number(Expr),
}
