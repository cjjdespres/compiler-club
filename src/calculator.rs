mod simple;

use simple::{ast, interpreter, parse, pretty, register_vm_1, stack_vm};

pub fn run_examples() {
    println!("First calculator example:");
    println!("{}", pretty::print(ast::example_1()));
    println!("Our interpreter says this is:");
    println!("{}", interpreter::interpret(&ast::example_1()));
    println!("We can even parse stuff!");
    let mut example_str = "2 + 2";
    let example_ast = parse::parse(&mut example_str).unwrap();
    println!("Here is the result of {} (just trust me)", example_str);
    println!("{}", interpreter::interpret(&example_ast));
    let stack_eval = stack_vm::eval(&example_ast);
    println!(
        "And our stack VM works too, because {} is {}",
        example_str, stack_eval
    );
    println!("Behold as well, the might of our stack optimizer, turning");
    println!("  {}", pretty::print(ast::example_2()));
    println!("into");
    println!(
        "  {}",
        pretty::print(stack_vm::stack_optimize(ast::example_2()))
    );
    println!(
        "Our register VM even works: {} is {}",
        pretty::print(ast::example_3()),
        register_vm_1::eval(&ast::example_3()).unwrap()
    );
}
