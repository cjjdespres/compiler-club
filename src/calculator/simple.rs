// Let's start with a simple calculator language, that supports addition,
// multiplication, and 64-bit integers. The semantics for this will be
// "whatever the analogous rust thing would do".

pub mod ast {
    #[derive(Debug)]
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

pub mod pretty {
    use super::ast::Expr;

    fn append(acc: &mut String, expr: Expr) -> () {
        match expr {
            Expr::Add(x, y) => {
                append(acc, *x);
                acc.push_str(" + ");
                append(acc, *y);
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
