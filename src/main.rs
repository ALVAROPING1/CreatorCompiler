use creator_parser::{architecture::Architecture, parser};

fn main() {
    let mut args = std::env::args();
    args.next();
    let operation = args
        .next()
        .expect("Expected operation code")
        .parse::<i32>()
        .expect("Expected operation code to be a number");
    if operation == 0 {
        println!("{}", Architecture::schema());
        return;
    }
    let filename = args.next().expect("Expected file argument");
    let arch = std::fs::read_to_string(filename).expect("We should be able to read the file");
    let arch = Architecture::from_json(&arch).expect("The input JSON should be correct");
    if operation == 1 {
        println!("{arch:#?}");
    } else {
        let filename = args.next().expect("Expected file argument");
        let src = std::fs::read_to_string(&filename).expect("We should be able to read the file");
        match parser::parse(&arch, &src) {
            Ok(ast) => println!("{ast:#?}"),
            Err(errors) => errors.print(&filename, &src),
        }
    }
}
