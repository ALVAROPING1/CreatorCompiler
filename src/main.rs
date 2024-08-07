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
    let src = std::fs::read_to_string(&filename).expect("We should be able to read the file");
    if operation == 1 {
        let arch = Architecture::from_json(&src).expect("The input JSON should be correct");
        println!("{arch:#?}");
    } else {
        parser::parse(&filename, &src);
    }
}
