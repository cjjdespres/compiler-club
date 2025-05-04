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

    pub fn interpret(expr: Expr) -> i64 {
        match expr {
            Expr::Add(x, y) => interpret(*x) + interpret(*y),
            Expr::Mul(x, y) => interpret(*x) * interpret(*y),
            Expr::Lit(x) => x,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_example_1() {
            assert_eq!(
                interpret(super::super::ast::example_1()),
                3 * 5 + (-7 + 11) * 9
            )
        }
    }
}

// A little stack VM as a compilation target for our calculator programs
pub mod stack_vm {
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
    fn compile_onto(expr: Expr, instrs: &mut Vec<Instr>) {
        match expr {
            Expr::Add(x, y) => {
                // For addition, we just need a program that computes x, then
                // computes y, then executes a single Add.
                compile_onto(*x, instrs);
                compile_onto(*y, instrs);
                instrs.push(Instr::Add)
            }
            Expr::Mul(x, y) => {
                // Same as Add
                compile_onto(*x, instrs);
                compile_onto(*y, instrs);
                instrs.push(Instr::Mul)
            }
            Expr::Lit(num) => instrs.push(Instr::Const(num)),
        }
    }

    pub fn compile(expr: Expr) -> Vec<Instr> {
        let mut instrs = Vec::new();
        compile_onto(expr, &mut instrs);
        instrs
    }

    pub fn eval(expr: Expr) -> i64 {
        let mut vm = execute(compile(expr));
        vm.pop()
    }

    #[cfg(test)]
    mod tests {
        use super::super::{ast, interpreter};
        use super::{compile, eval, Instr};

        #[test]
        fn test_example_1_compiles() {
            assert_eq!(
                compile(ast::example_1()),
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
                eval(ast::example_1()),
                interpreter::interpret(ast::example_1())
            )
        }
    }
}
