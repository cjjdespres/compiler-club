mod simple;

use simple::{ast, interpreter, parse, pretty};

pub fn run_examples() {
    println!("First calculator example:");
    println!("{}", pretty::print(ast::example_1()));
    println!("This evaluates to:");
    println!("{}", interpreter::interpret(ast::example_1()));
    println!("We can even parse stuff!");
    let mut example_str = "2 + 2";
    println!("Here is the result of {} (just trust me)", example_str);
    println!(
        "{}",
        interpreter::interpret(parse::parse(&mut example_str).unwrap())
    );
}
