mod simple;

use simple::{ast, interpreter, parse, pretty, stack_vm};

pub fn run_examples() {
    println!("First calculator example:");
    println!("{}", pretty::print(ast::example_1()));
    println!("Our interpreter says this is:");
    println!("{}", interpreter::interpret(ast::example_1()));
    println!("We can even parse stuff!");
    let mut example_str = "2 + 2";
    println!("Here is the result of {} (just trust me)", example_str);
    println!(
        "{}",
        interpreter::interpret(parse::parse(&mut example_str).unwrap())
    );
    let stack_eval = stack_vm::eval(parse::parse(&mut example_str).unwrap());
    println!(
        "And our stack VM works too, because {} is {}",
        example_str, stack_eval
    )
}
