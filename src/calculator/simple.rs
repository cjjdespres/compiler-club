// Let's start with a simple calculator language, that supports addition,
// multiplication, and 64-bit integers. The semantics for this will be "whatever
// the analogous rust thing would do".

pub mod ast {
    #[derive(Debug, PartialEq)]
    pub enum Expr {
        Add(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
        Lit(i64),
    }
    pub fn add(x: Expr, y: Expr) -> Expr {
        Expr::Add(Box::new(x), Box::new(y))
    }
    pub fn mul(x: Expr, y: Expr) -> Expr {
        Expr::Mul(Box::new(x), Box::new(y))
    }
    pub fn lit(x: i64) -> Expr {
        Expr::Lit(x)
    }

    // One example: 3 * 5 + (-7 + 11) * 9
    pub fn example_1() -> Expr {
        add(mul(lit(3), lit(5)), mul(add(lit(-7), lit(11)), lit(9)))
    }

    // A second example for our stack optimizer
    pub fn example_2() -> Expr {
        add(lit(1), add(lit(2), add(lit(3), lit(4))))
    }

    // A very simple third example
    pub fn example_3() -> Expr {
        add(lit(5), lit(3))
    }
}

// Start with the lexers. All of these will consume optional trailing
// whitespace, so the input stream will be left on the (hopefully valid)
// next token.
//
// N.B. winnow seems to be oriented toward concrete parsers looking like
//
// fn parser(input: &mut Input) -> Result<Out, Err>
//
// so that's what I do here. That's basically what impl Parser<...> is. For
// actual combinators, it seems better to accept a generic F : impl
// Parser<...> (see lex_ws for an example).
//
// All of the concrete parsers could instead have been
//
// fn parser() -> impl Parser<Input, Output, Err>
//
// i.e., zero-arity combinators. The representation is nearly identical,
// except that in the `() -> impl` way you need to write `parser()` to have
// an actual Parser, whereas in the `Input -> Result` way it's `parser`
// that's the parser. I'm unsure of the performance difference, if any.
//
// A downside of doing it with the explicit input is that you have to write
// ".parse_next(input)" a ton.
//
// N.B. You can write
//
// fn parser() -> impl Parser<Input, Output, Err> {
//     move |input: &mut Input| {
//         <do stuff using input, including parse_next et al.>
//     }
// }
//
// if you want to do it the impl combinator way and still have access to the
// explicit input.
pub mod lex {
    // I'm being lazy and not implementing my own parser-combinator library. Also no
    // errors - they are for the weak.
    use winnow::ascii;
    use winnow::combinator;
    use winnow::error::ErrMode;
    use winnow::token;
    use winnow::Parser;

    pub fn ws<'a>(input: &mut &'a str) -> Result<&'a str, ErrMode<()>> {
        Parser::take(token::take_while(0.., |c| c == ' ' || c == '\n')).parse_next(input)
    }

    pub fn lex_ws<'a, F, O>(inner: F) -> impl Parser<&'a str, O, ErrMode<()>>
    where
        F: Parser<&'a str, O, ErrMode<()>>,
    {
        combinator::terminated(inner, ws)
    }

    pub fn lparen<'a>(input: &mut &'a str) -> Result<char, ErrMode<()>> {
        lex_ws('(').parse_next(input)
    }

    pub fn rparen<'a>(input: &mut &'a str) -> Result<char, ErrMode<()>> {
        lex_ws(')').parse_next(input)
    }

    // Note that this add lexer overlaps lexically with the start of an
    // explicitly-signed positive integer. So, if we're ever in a situation
    // where both can appear, we'll have to choose which one will take
    // precedence. (It doesn't matter that much syntactically at the
    // moment).
    pub fn add<'a>(input: &mut &'a str) -> Result<char, ErrMode<()>> {
        lex_ws('+').parse_next(input)
    }

    pub fn mul<'a>(input: &mut &'a str) -> Result<char, ErrMode<()>> {
        lex_ws('*').parse_next(input)
    }

    pub fn sign<'a>(input: &mut &'a str) -> Result<char, ErrMode<()>> {
        lex_ws(combinator::alt(('+', '-'))).parse_next(input)
    }

    // Semi-lazy, but okay. If we had errors, it would be nice to point out
    // the fact that the literal is too big if str::parse fails.
    pub fn lit<'a>(input: &mut &'a str) -> Result<i64, ErrMode<()>> {
        lex_ws(
            Parser::take((
                combinator::opt(sign),
                // "Accumulate" into () (i.e., ignore what we parse), then take the
                // whole chunk at the end and attempt to turn it into an i64.
                combinator::repeat::<_, _, (), _, _>(1.., ascii::digit1.map(|_| ())),
            ))
            .try_map(str::parse),
        )
        .parse_next(input)
    }
    #[cfg(test)]
    mod tests {
        use winnow::{combinator, error::ParseError, Parser};

        use super::*;

        // Mostly just for tests/showing off, because the higher-level parse
        // module will still operate on the same str input.
        #[derive(Clone, Debug, PartialEq)]
        pub enum Token {
            Add,
            Mul,
            Lparen,
            Rparen,
            Lit(i64),
        }

        pub fn tokens<'a>(input: &mut &'a str) -> Result<Vec<Token>, ParseError<&'a str, ()>> {
            combinator::repeat(
                0..,
                combinator::alt((
                    lit.map(Token::Lit),
                    add.value(Token::Add),
                    mul.value(Token::Mul),
                    lparen.value(Token::Lparen),
                    rparen.value(Token::Rparen),
                )),
            )
            .parse(input)
        }

        #[test]
        fn test_example_1() {
            let source_str = &mut "3 * 5 + (-7 + 11) * 9";
            assert_eq!(
                tokens(source_str).unwrap(),
                vec![
                    Token::Lit(3),
                    Token::Mul,
                    Token::Lit(5),
                    Token::Add,
                    Token::Lparen,
                    Token::Lit(-7),
                    Token::Add,
                    Token::Lit(11),
                    Token::Rparen,
                    Token::Mul,
                    Token::Lit(9)
                ]
            )
        }
    }
}

// At this point it might be helpful to have an actual grammar in mind.
// We'd like to start with the easy:
//
// <expr> ->
//     <expr> '+' <expr>   // addition
//     <expr> '*' <expr>   // multiplication
//     '(' <expr> ')'      // parenthesis
//     <lit>               // integer literals
//
// except that doesn't work with recursive descent - in the addition
// production, we'll always descend into the first <expr>, make no progress,
// and eventually stack overflow.
//
// We have to guide our parser along by stratifying the grammar:
//
// <expr> ->
//     <atom> '+' <atom>
//     <atom> '*' <atom>
//     <atom>
// <atom> ->
//     '(' <expr> ')'
//     <lit>
//
// This solves the progress issue, but is a little too restrictive - it
// forces us to parenthesize every expression that isn't a literal or at the
// top level. This is incompatible with the comment next to our
// ast::example_1 - it claims that the source for that example is "3 * 5 +
// (-7 + 11) * 9", and in that expression it's clearly possible to add two
// unparenthesized multiplication expressions together.
//
// So, we have to be a little more careful, and add in some operator
// precedence:
//
// <expr> ->
//     <expr_no_add> '+' <expr_no_add>
//     <expr_no_add>
//
// <expr_no_add> ->
//     <atom> '*' <atom>
//     <atom>
//
// <atom> ->
//     '(' <expr> ')'
//     <lit>
//
// This is a grammar with operator precedence ('+' is weaker than '*') but
// with no associativity (we forbid "3 + 5 + 7" or "3 * 5 * 7" entirely).
// This is compatible with our pretty-printer, which is still a little too
// parenthesis-happy. The grammar could also be left-factored a bit more, so
// parsing an expr won't double-parse as much, but this is okay for now.
pub mod parse {
    use super::lex;
    use super::*;
    use ast::Expr;
    use winnow::error::{ErrMode, ParseError};
    use winnow::{combinator, Parser};

    pub fn add<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        (expr_no_add, lex::add, expr_no_add)
            .map(|(e1, _, e2)| ast::add(e1, e2))
            .parse_next(input)
    }
    pub fn mul<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        (atom, lex::mul, atom)
            .map(|(e1, _, e2)| ast::mul(e1, e2))
            .parse_next(input)
    }

    pub fn lit<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        lex::lit.map(ast::lit).parse_next(input)
    }

    pub fn parenthetical<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        combinator::delimited(lex::lparen, expr, lex::rparen).parse_next(input)
    }

    pub fn atom<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        combinator::alt((parenthetical, lit)).parse_next(input)
    }

    pub fn expr_no_add<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        combinator::alt((mul, atom)).parse_next(input)
    }

    pub fn expr<'a>(input: &mut &'a str) -> Result<Expr, ErrMode<()>> {
        combinator::alt((add, expr_no_add)).parse_next(input)
    }

    pub fn parse<'a>(input: &mut &'a str) -> Result<Expr, ParseError<&'a str, ()>> {
        expr.parse(input)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_example_1() {
            let source_str = &mut "3 * 5 + (-7 + 11) * 9";
            assert_eq!(parse::parse(source_str).unwrap(), ast::example_1())
        }
    }
}

pub mod pretty {
    use super::ast::Expr;

    // N.B. we can relax the parentheses by introducing precedence/associativity
    // into the pretty-printing, though if we add associativity then we'll need
    // to modify our parser to compensate.
    fn append(acc: &mut String, expr: Expr) -> () {
        match expr {
            Expr::Add(x, y) => {
                acc.push('(');
                append(acc, *x);
                acc.push_str(") + (");
                append(acc, *y);
                acc.push(')');
            }
            Expr::Mul(x, y) => {
                acc.push('(');
                append(acc, *x);
                acc.push_str(") * (");
                append(acc, *y);
                acc.push(')');
            }
            Expr::Lit(x) => acc.push_str(&x.to_string()),
        }
    }

    // A simple pretty-printing function with far too many parentheses
    pub fn print(expr: Expr) -> String {
        let mut acc = String::new();
        append(&mut acc, expr);
        return acc;
    }

    #[cfg(test)]
    mod tests {
        use super::super::ast;
        use super::super::parse;
        use super::super::pretty;

        #[test]
        fn round_trip_1() {
            let pretty_str = pretty::print(ast::example_1());
            assert_eq!(
                ast::example_1(),
                parse::parse(&mut pretty_str.as_str()).unwrap()
            )
        }
    }
}

// Our initial runtime is the host language itself
pub mod interpreter {
    use super::ast::Expr;

    pub fn interpret(expr: &Expr) -> i64 {
        match expr {
            Expr::Add(x, y) => interpret(x) + interpret(y),
            Expr::Mul(x, y) => interpret(x) * interpret(y),
            Expr::Lit(x) => *x,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_example_1() {
            assert_eq!(
                interpret(&super::super::ast::example_1()),
                3 * 5 + (-7 + 11) * 9
            )
        }
    }
}

// A little stack VM as a compilation target for our calculator programs
pub mod stack_vm {
    use std::cmp::{max, min};

    use super::ast;
    use super::ast::Expr;

    // Our VM can:
    // 1. pop two numbers off the stack and push their sum onto the stack
    // 2. pop two numbers off the stack and push their product onto the stack
    // 3. push an integer constant onto the stack
    #[derive(Debug, PartialEq)]
    pub enum Instr {
        Add,
        Mul,
        Const(i64),
    }

    pub struct VM {
        stack: Vec<i64>,
    }

    // Like all good VMs, we simply declare that it is UB to attempt to execute
    // an instr against a stack that isn't in the correct state for it. In
    // practice, that means we can be lazy and panic whenever anything might go
    // wrong.
    //
    // We'd never generate an incorrect program, obviously, so that disclaimer
    // is irrelevant.
    impl VM {
        pub fn new() -> Self {
            Self { stack: Vec::new() }
        }

        pub fn pop(&mut self) -> i64 {
            self.stack.pop().unwrap()
        }

        pub fn push(&mut self, num: i64) {
            self.stack.push(num)
        }

        pub fn step(&mut self, instr: Instr) {
            match instr {
                Instr::Add => {
                    let x = self.pop();
                    let y = self.pop();
                    self.push(x + y)
                }
                Instr::Mul => {
                    let x = self.pop();
                    let y = self.pop();
                    self.push(x * y)
                }
                Instr::Const(num) => self.push(num),
            }
        }

        pub fn execute_all(&mut self, instrs: Vec<Instr>) {
            for instr in instrs {
                self.step(instr)
            }
        }
    }

    pub fn execute(instrs: Vec<Instr>) -> VM {
        let mut vm = VM::new();
        vm.execute_all(instrs);
        vm
    }

    // Compile the given expression and add the instructions to the accumulator.
    // The result is a program that does whatever the accumulator did, then
    // additionally pushes the result of evaluating the expression onto the
    // stack.
    fn compile_onto(expr: &Expr, instrs: &mut Vec<Instr>) {
        match expr {
            Expr::Add(x, y) => {
                // For addition, we just need a program that computes x, then
                // computes y, then executes a single Add.
                compile_onto(x, instrs);
                compile_onto(y, instrs);
                instrs.push(Instr::Add)
            }
            Expr::Mul(x, y) => {
                // Same as Add
                compile_onto(x, instrs);
                compile_onto(y, instrs);
                instrs.push(Instr::Mul)
            }
            Expr::Lit(num) => instrs.push(Instr::Const(*num)),
        }
    }

    pub fn compile(expr: &Expr) -> Vec<Instr> {
        let mut instrs = Vec::new();
        compile_onto(expr, &mut instrs);
        instrs
    }

    pub fn eval(expr: &Expr) -> i64 {
        let mut vm = execute(compile(expr));
        vm.pop()
    }

    // We can even write a little optimization pass for our programs. This one
    // will operate on the Expr itself, because that's a little easier for this
    // one.
    //
    // Some expressions, like 1 + (2 + (3 + 4)), take up a lot of stack space in
    // their evaluation; that example becomes
    //
    // lit 1
    // lit 2
    // lit 3
    // lit 4
    // add
    // add
    // add
    //
    // and it takes up to 4 stack slots during execution. Any right-associated
    // calculator program will exhibit this kind of stack growth. Since our
    // integer arithmetic is commutative, we could transform this into
    //
    // lit 3
    // lit 4
    // add
    // lit 2
    // add
    // lit 1
    // add
    //
    // Our stack size is now 2; in fact, applying this kind of transformation to
    // any amount of additions will result in a program that takes up at most
    // two stack slots! One is effectively an accumulator, and one is basically
    // just a temporary stack slot to hold an integer immediate.
    //
    // We'll implement it with a size-based heuristic:
    //
    // 1. A single literal optimizes to itself, of course.
    //
    // 2. An (x + y) expression will be reordered to (y + x) if it looks like y
    //    will take up _more_ stack slots at maximum than x. Why more? One way
    //    to think of it is in terms of "stack pressure" - when we evaluate x +
    //    y we leave the result of evaluating x on the stack the entire time we
    //    evaluate y. That intermediate result from evaluating the first term
    //    adds to the pressure on the stack when we evaluate the second term. If
    //    we can see that one of the expressions is low-pressure, we can arrange
    //    for the intermediate result to stick around while it evaluates. That
    //    shifts pressure from a high-pressure evaluation to a low-pressure
    //    evaluation, and the result is a reduction in max pressure. The
    //    max_stack function below will make this a little clearer, hopefully.
    //
    // This optimization will be applied recursively, of course.
    //
    // We could do this by reassociating the arithmetic as well. Also, if we had
    // stack manipulation instructions in our VM then we could even implement
    // this without needing either; with a hypothetical swap instruction we
    // could do
    //
    // lit 3
    // lit 4
    // add
    // lit 2
    // swap
    // add
    // lit 1
    // swap
    // add
    //
    // which would compute exactly 1 + (2 + (3 + 4)), just in a different
    // evaluation order.
    pub fn stack_optimize(expr: Expr) -> Expr {
        // we could be a bit cleverer, and estimate the necessary stack size at
        // the same time we optimize the expression, but this nicely separates
        // the two parts of the algorithm. Also I'm lazy. Also this needs to be
        // a fn because it's recursive.
        fn max_stack(expr: &Expr) -> i64 {
            // If we execute x <op> y in that order, we need at least
            // max_stack(x) to evaluate x, and at least max_stack(y) + 1 to
            // evaluate y (because the evaluation of x needs to stick
            // around). But, we have the power of reordering, so we need to
            // estimate the stack size of y <op> x too, and take the minimum of
            // those two estimates.

            let max_of_binop = |x: &Expr, y: &Expr| {
                let x_est = max_stack(x);
                let y_est = max_stack(y);
                let x_y_est = max(x_est, y_est + 1);
                let y_x_est = max(y_est, x_est + 1);
                min(x_y_est, y_x_est)
            };
            match expr {
                Expr::Add(x, y) => max_of_binop(x, y),
                Expr::Mul(x, y) => max_of_binop(x, y),
                Expr::Lit(_) => 1,
            }
        }

        match expr {
            Expr::Add(x, y) => {
                let x = stack_optimize(*x);
                let y = stack_optimize(*y);
                if max_stack(&y) > max_stack(&x) {
                    ast::add(y, x)
                } else {
                    ast::add(x, y)
                }
            }
            Expr::Mul(x, y) => {
                let x = stack_optimize(*x);
                let y = stack_optimize(*y);
                if max_stack(&y) > max_stack(&x) {
                    ast::mul(y, x)
                } else {
                    ast::mul(x, y)
                }
            }
            Expr::Lit(_) => expr,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::super::{ast, interpreter};
        use super::{compile, eval, stack_optimize, Instr};

        #[test]
        fn test_example_1_compiles() {
            assert_eq!(
                compile(&ast::example_1()),
                vec![
                    Instr::Const(3),
                    Instr::Const(5),
                    Instr::Mul,
                    Instr::Const(-7),
                    Instr::Const(11),
                    Instr::Add,
                    Instr::Const(9),
                    Instr::Mul,
                    Instr::Add
                ]
            )
        }

        #[test]
        fn test_example_1_runs_like_interpreter() {
            assert_eq!(
                eval(&ast::example_1()),
                interpreter::interpret(&ast::example_1())
            )
        }

        #[test]
        fn test_example_2_optimizes() {
            assert_eq!(
                stack_optimize(ast::example_2()),
                ast::add(
                    ast::add(ast::add(ast::lit(3), ast::lit(4)), ast::lit(2)),
                    ast::lit(1)
                )
            )
        }
    }
}

// Now we'll proceed to a small register-based VM. It will have a set of
// _locations_ that hold numbers in them. Instructions operate entirely on
// locations - they read values in source locations, perform some simple
// operation on those values, and store the result in a destination location.
pub mod register_vm_1 {
    use super::ast::Expr;

    // All the locations are deliberately uni-typed
    type Loc = i64;

    type SrcLoc = Loc;

    type DstLoc = Loc;

    #[derive(Debug, PartialEq)]
    pub enum Instr {
        // Add the values in the source locations and store the result in the
        // destination location
        Add(DstLoc, SrcLoc, SrcLoc),
        // Multiply the values in the source locations and store the result in the
        // destination location
        Mul(DstLoc, SrcLoc, SrcLoc),
        // Load the constant into the destination location
        Imm(DstLoc, i64),
    }

    pub struct VM {
        registers: Vec<i64>,
    }

    const MAX_LOC: Loc = 8;

    impl VM {
        pub fn new() -> Self {
            Self {
                // No one could ever need more than 8 locations
                registers: vec![0; MAX_LOC as usize],
            }
        }

        // Just like real life CPUs, if you try to execute a malformed
        // instruction this VM simply explodes
        fn index_from_loc(&self, loc: Loc) -> usize {
            let idx = loc as usize;
            if loc < 0 || idx >= self.registers.len() {
                panic!("At the disco")
            }
            idx
        }

        pub fn read(&self, src: SrcLoc) -> i64 {
            let idx = self.index_from_loc(src);
            self.registers[idx]
        }

        pub fn write(&mut self, dst: DstLoc, val: i64) {
            let idx = self.index_from_loc(dst);
            self.registers[idx] = val;
        }

        pub fn execute(&mut self, instr: Instr) {
            match instr {
                Instr::Add(dst, x_loc, y_loc) => {
                    let x = self.read(x_loc);
                    let y = self.read(y_loc);
                    self.write(dst, x + y)
                }
                Instr::Mul(dst, x_loc, y_loc) => {
                    let x = self.read(x_loc);
                    let y = self.read(y_loc);
                    self.write(dst, x * y)
                }
                Instr::Imm(dst, x) => self.write(dst, x),
            }
        }

        pub fn execute_all(instrs: Vec<Instr>) -> VM {
            let mut vm = VM::new();
            for instr in instrs {
                vm.execute(instr)
            }
            vm
        }
    }

    // Compilation is going to be a little more difficult with locations,
    // because we have to keep track of the "live" locations - the locations
    // with values in them that we need to keep around for use in other parts of
    // the compilation. We didn't have this problem with the stack-based VM
    // because the operation of the stack naturally gave us an isolated space in
    // which to evaluate each expression. That's how we could create a program
    // that evaluates two expressions X and Y simply by concatenating the
    // programs that evaluate X and Y individually.
    //
    // We also have decide on a convention for "returning" the result of a
    // program. In our stack programs, the result was naturally left at the top
    // of the stack.

    // In this first attempt, we'll obey a simple recursive code generation
    // scheme for a given expr:
    //
    // 1. The first open location will always be reserved to store the
    //    result of evaluating the expression. This solves the return
    //    problem - the whole program will put its result in location 0.
    //
    // 2. A literal expression will get turned into an Imm
    //
    // 3. An Add or Mul expression will be compiled like it was with the
    //    stack_vm - we'll generate a program to evaluate the first operand,
    //    then generate a program to evaluate the second, then emit a single
    //    Add/Mul instruction to put the final result in the return
    //    location. The difference between this and the stack_vm is that we
    //    now have to track free locations and return locations ourselves.

    // Our code gen only needs to keep track of the next free location,
    // since our code gen only uses locations starting at the next free
    // location and going upward.
    pub struct CodeGenState {
        next_free_loc: Loc,
    }

    // While our VM still has the (perhaps temporary) luxury of exploding
    // whenever something goes wrong, we'd rather our compiler not explode
    // if given a difficult program.
    #[derive(Debug, PartialEq)]
    pub enum CodeGenError {
        // We needed a new location, but the next free one was too big
        RanOutOfLocations(Loc),
    }

    fn err_ran_out_of_locations<O>(loc: Loc) -> Result<O, CodeGenError> {
        Err(CodeGenError::RanOutOfLocations(loc))
    }

    impl CodeGenState {
        pub fn new() -> Self {
            Self { next_free_loc: 0 }
        }

        pub fn new_loc(&mut self) -> Result<Loc, CodeGenError> {
            let loc = self.next_free_loc;
            if loc >= MAX_LOC {
                err_ran_out_of_locations(loc)
            } else {
                self.next_free_loc += 1;
                Ok(loc)
            }
        }

        // We might as well implement some simple location reclamation while
        // we're here. Our code gen only ever uses the next free location
        // and beyond for storage, and when a program is done executing only
        // the result location (the initial next free location) contains
        // anything important. Thus we can safely mark everything beyond the
        // result location as free after generating a particular program.
        pub fn reclaim_beyond(&mut self, loc: Loc) {
            self.next_free_loc = loc + 1;
        }
    }

    // Compiled programs get a little more complex now, since we have to
    // keep track of where the return location is. Well, given the code gen
    // conventions outlied above, we could technically just read the DstLoc
    // from the final instruction to get the return location, but that might
    // be going a little too far.
    #[derive(Debug, PartialEq)]
    pub struct Program {
        instructions: Vec<Instr>,
        return_loc: DstLoc,
    }

    impl Program {
        // Return a new empty program with the given return location. The
        // result of executing it will be undefined, as we don't clear the
        // return location by default.
        pub fn new(return_loc: DstLoc) -> Self {
            Self {
                instructions: Vec::new(),
                return_loc,
            }
        }

        pub fn push_instr(&mut self, instr: Instr) {
            self.instructions.push(instr)
        }

        pub fn push_instrs(&mut self, instrs: Vec<Instr>) {
            for instr in instrs {
                self.push_instr(instr);
            }
        }
    }

    fn compile_binop_for<F>(
        codegen: &mut CodeGenState,
        top_program: &mut Program,
        binop_instr: F,
        x: &Expr,
        y: &Expr,
    ) -> Result<(), CodeGenError>
    where
        F: Fn(DstLoc, SrcLoc, SrcLoc) -> Instr,
    {
        // Generate a program to compute x
        let x_program = compile_expr(codegen, x)?;
        top_program.push_instrs(x_program.instructions);
        codegen.reclaim_beyond(x_program.return_loc);

        // And one to compute y
        let y_program = compile_expr(codegen, y)?;
        top_program.push_instrs(y_program.instructions);
        codegen.reclaim_beyond(y_program.return_loc);

        // The overall program is one that computes x, then y, then
        // puts the sum of those two results into the overall return
        // location.
        let result_instr = binop_instr(
            top_program.return_loc,
            x_program.return_loc,
            y_program.return_loc,
        );
        top_program.push_instr(result_instr);
        return Ok(());
    }

    pub fn compile_expr(codegen: &mut CodeGenState, expr: &Expr) -> Result<Program, CodeGenError> {
        let return_loc = codegen.new_loc()?;
        let mut program = Program::new(return_loc);

        match expr {
            Expr::Lit(num) => {
                // Just load the literal into the return location
                let lit_instr = Instr::Imm(return_loc, *num);
                program.push_instr(lit_instr);
            }
            Expr::Add(x, y) => compile_binop_for(codegen, &mut program, Instr::Add, x, y)?,
            Expr::Mul(x, y) => compile_binop_for(codegen, &mut program, Instr::Mul, x, y)?,
        }

        return Ok(program);
    }

    pub fn compile(expr: Expr) -> Result<Program, CodeGenError> {
        let mut codegen = CodeGenState::new();
        compile_expr(&mut codegen, &expr)
    }

    pub fn eval(expr: Expr) -> Result<i64, CodeGenError> {
        let program = compile(expr)?;
        let vm = VM::execute_all(program.instructions);
        Ok(vm.read(program.return_loc))
    }

    #[cfg(test)]
    mod tests {
        use super::super::super::{ast, interpreter};
        use super::*;

        #[test]
        fn example_3_compiles() {
            assert_eq!(
                compile(ast::example_3()),
                Ok(Program {
                    instructions: vec![Instr::Imm(1, 5), Instr::Imm(2, 3), Instr::Add(0, 1, 2)],
                    return_loc: 0
                })
            )
        }

        #[test]
        fn example_3_evaluates() {
            assert_eq!(
                eval(ast::example_3()).unwrap(),
                interpreter::interpret(&ast::example_3())
            )
        }

        #[test]
        fn example_1_compiles() {
            assert_eq!(
                compile(ast::example_1()),
                Ok(Program {
                    instructions: vec![
                        Instr::Imm(2, 3),
                        Instr::Imm(3, 5),
                        Instr::Mul(1, 2, 3),
                        Instr::Imm(4, -7),
                        Instr::Imm(5, 11),
                        Instr::Add(3, 4, 5),
                        Instr::Imm(4, 9),
                        Instr::Mul(2, 3, 4),
                        Instr::Add(0, 1, 2)
                    ],
                    return_loc: 0
                })
            )
        }

        #[test]
        fn example_1_evaluates() {
            assert_eq!(
                eval(ast::example_1()).unwrap(),
                interpreter::interpret(&ast::example_1())
            )
        }
    }
}
