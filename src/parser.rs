use ariadne::{sources, Color, Label, Report, ReportKind};
use chumsky::prelude::*;
use std::fmt;

mod expression;
use expression::Expr;

use crate::architecture::{Architecture, DirectiveAction};

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
enum Token {
    Number(String),
    String(String),
    Character(char),
    Identifier(String),
    Operator(char),
    Ctrl(char),
    Literal(char),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{n}"),
            Self::String(s) => write!(f, "{s}"),
            Self::Identifier(i) => write!(f, "{i}"),
            Self::Ctrl(c) | Self::Operator(c) | Self::Literal(c) | Self::Character(c) => {
                write!(f, "{c}")
            }
        }
    }
}

type Span = std::ops::Range<usize>;
type Spanned<T> = (T, Span);

fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    // let newline = text::newline().to('\n');

    // Numbers
    let num = text::int(10).map(Token::Number).labelled("number");

    // Expression operators
    let op = one_of("+-*/%|&^~")
        .map(Token::Operator)
        .labelled("operator");

    // Control characters used in the grammar
    let ctrl = one_of(":,.\n")
        .map(Token::Ctrl)
        .labelled("control character");

    // Other literal punctuation characters. This should be the last option if all other patterns
    // fail, so we don't need to be too specific to avoid ambiguities with other patterns
    let literal = filter(|c: &char| c.is_ascii_punctuation())
        .map(Token::Literal)
        .labelled("literal");

    // Name identifiers
    let identifier = filter(|c: &char| c.is_ascii_alphabetic())
        .chain(filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_' || *c == '.').repeated())
        .collect::<String>()
        .map(Token::Identifier)
        .labelled("identifier");

    // TODO: implement escape sequences
    // Literal strings (`"..."`)
    let string = just('"')
        .ignore_then(just('"').not().repeated())
        .then_ignore(just('"'))
        .collect::<String>()
        .map(Token::String);

    // Literal characters (`'c'`)
    let character = just('\'')
        .ignore_then(just('\'').not())
        .then_ignore(just('\''))
        .or(just("'\\\''").to('\''))
        .map(Token::Character);

    // Any of the previous patterns can be a token
    let token = choice((num, op, ctrl, identifier, string, character, literal)).labelled("token");

    // Single line comments
    let comment = just("#")
        .then(just('\n').not().repeated())
        .padded()
        .labelled("comment");

    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(comment.repeated())
        .padded_by(
            filter(|c: &char| c.is_whitespace() && *c != '\n')
                .ignored()
                .repeated(),
        )
        .repeated()
        .then_ignore(end())
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
    args: Vec<Expr>,
}

#[derive(Debug)]
enum ASTNode {
    CodeSegment(Vec<InstructionNode>),
    DataSegment(Vec<DataNode>),
}

fn parser<'a>(
    arch: &'a Architecture,
) -> impl Parser<Token, Vec<ASTNode>, Error = Simple<Token>> + 'a {
    let ident = select! { Token::Identifier(ident) => ident }.labelled("identifier");
    // TODO: allow new lines between labels
    let label = ident.then_ignore(just(Token::Ctrl(':'))).labelled("label");

    let directive = just(Token::Ctrl('.'))
        .ignore_then(ident)
        .map(|ident| format!(".{ident}"))
        .labelled("directive name");

    let labels = label.repeated().collect().labelled("labels");

    let data_directive = labels
        .clone()
        .then(directive.clone())
        .then(
            expression::parser()
                // TODO: allow new lines between values
                .separated_by(just(Token::Ctrl(',')))
                .labelled("parameters"),
        )
        .then_ignore(just(Token::Ctrl('\n')))
        .map(|((labels, name), args)| DataNode { labels, name, args })
        .labelled("data directive");

    let data_segment_directive = arch
        .find_directive(DirectiveAction::DataSegment)
        .expect("The data segment directive should be defined");
    let code_segment_directive = arch
        .find_directive(DirectiveAction::CodeSegment)
        .expect("The code segment directive should be defined");

    let data_segment = directive
        .clone()
        .then_ignore(just(Token::Ctrl('\n')))
        .try_map(move |name: String, span| {
            if name == data_segment_directive {
                Ok(())
            } else {
                Err(Simple::custom(span, "TODO: error message data"))
            }
        })
        .ignore_then(data_directive.repeated())
        .map(ASTNode::DataSegment);

    let instruction = labels
        .then(ident)
        .then(take_until(just(Token::Ctrl('\n'))).map_with_span(|(args, _), span| (args, span)))
        .map(|((labels, name), args)| InstructionNode { labels, name, args })
        .labelled("instruction");

    let code_segment = directive
        .clone()
        .then_ignore(just(Token::Ctrl('\n')))
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
