use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;

mod expression;
use expression::Expr;

mod lexer;
use lexer::{lexer, Token};

use crate::architecture::{Architecture, DirectiveAction};

type Span = std::ops::Range<usize>;
type Spanned<T> = (T, Span);

macro_rules! Parser {
    ($i:ty, $o:ty) => { impl Parser<$i, $o, Error = Simple<$i>> + Clone };
    ($i:ty, $o:ty, $lt:lifetime) => { impl Parser<$i, $o, Error = Simple<$i>> + Clone + $lt };
}
use Parser;

#[derive(Debug)]
enum Data {
    String(String),
    Number(Expr),
}

#[derive(Debug)]
struct InstructionNode {
    labels: Vec<String>,
    name: String,
    args: Spanned<Vec<Token>>,
}

#[derive(Debug)]
struct DataNode {
    labels: Vec<String>,
    name: String,
    args: Vec<Data>,
}

#[derive(Debug)]
enum ASTNode {
    CodeSegment(Vec<InstructionNode>),
    DataSegment(Vec<DataNode>),
}

fn parser<'a>(arch: &'a Architecture) -> Parser!(Token, Vec<ASTNode>, 'a) {
    // Identifiers
    let ident = select! { Token::Identifier(ident) => ident }.labelled("identifier");
    // Newline token
    let newline = || just(Token::Ctrl('\n'));

    // Labels: `label -> ident:`
    let label = ident
        .then_ignore(just(Token::Ctrl(':')))
        .padded_by(newline().repeated())
        .labelled("label");

    // Directives: `directive -> .ident`
    let directive = just(Token::Ctrl('.'))
        .ignore_then(ident)
        .map(|ident| format!(".{ident}"))
        .labelled("directive name");

    // Any amount of labels: `labels -> label*`
    let labels = label.repeated().collect().labelled("labels");

    // Data statement: statements within the data segment
    // `data_statement -> labels directive expression (, expression)*`
    let data_statement = labels
        .clone()
        .then(directive.clone())
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
                        .or(select! {Token::String(s) => Data::String(s)}),
                )
                .then_ignore(
                    newline()
                        .repeated()
                        .then(just(Token::Ctrl(',')).rewind())
                        .or_not(),
                )
                .separated_by(just(Token::Ctrl(',')))
                .at_least(1)
                .labelled("parameters"),
        )
        .then_ignore(newline())
        .map(|((labels, name), args)| DataNode { labels, name, args })
        .labelled("data directive");

    // Name of the directive changing to the data segment
    let data_segment_directive = arch
        .find_directive(DirectiveAction::DataSegment)
        .expect("The data segment directive should be defined");
    // Name of the directive changing to the code segment
    let code_segment_directive = arch
        .find_directive(DirectiveAction::CodeSegment)
        .expect("The code segment directive should be defined");

    // Data segment: `data_segment -> data_segment_directive data_statement*`
    let data_segment = directive
        .clone()
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
        .then(ident)
        .then(take_until(newline()).map_with_span(|(args, _), span| (args, span)))
        .map(|((labels, name), args)| InstructionNode { labels, name, args })
        .labelled("instruction");

    // Code segment: `code_segment -> code_segment_directive instruction*`
    let code_segment = directive
        .clone()
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

pub fn parse(arch: &Architecture, filename: &String, src: &str) {
    let (tokens, errs) = lexer().parse_recovery(src);

    let parse_errs = tokens.map_or_else(Vec::new, |tokens| {
        let len = src.chars().count();
        #[allow(clippy::range_plus_one)] // Chumsky requires an inclusive range to avoid type errors
        let (ast, parse_errs) = parser(arch).parse_recovery(chumsky::stream::Stream::from_iter(
            len..len + 1,
            tokens.into_iter(),
        ));
        if let Some(ast) = ast {
            println!("ast: {ast:#?}");
        }
        parse_errs
    });
    errs.into_iter()
        .map(|e| e.map(|c| c.to_string()))
        .chain(parse_errs.into_iter().map(|e| e.map(|tok| tok.to_string())))
        .for_each(|e| {
            Report::build(ReportKind::Error, filename, e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new((
                        filename.clone(),
                        std::convert::Into::<std::ops::Range<_>>::into(e.span()),
                    ))
                    .with_message(format!("{:?}", e.reason()))
                    .with_color(Color::Red),
                )
                .with_labels(e.label().map_or_else(Vec::new, |label| {
                    vec![Label::new((
                        filename.clone(),
                        std::convert::Into::<std::ops::Range<_>>::into(e.span()),
                    ))
                    .with_message(format!("while parsing this {label}"))
                    .with_color(Color::Yellow)]
                }))
                .finish()
                .print(sources([(filename.clone(), src)]))
                .expect("we should be able to print to stdout");
        });
}
