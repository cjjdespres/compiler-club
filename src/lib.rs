mod calculator;

use calculator::simple::{ast, interpreter, pretty};

pub fn run_examples() {
    println!("First calculator example:");
    println!("{}", pretty::print(ast::example_1()));
    println!("This evaluates to:");
    println!("{}", interpreter::interpret(ast::example_1()));
}
