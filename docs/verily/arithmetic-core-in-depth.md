With the vagueness of [the introduction to the core](./core-intro.md) out of the
way, we can get into the structure of the core a bit more. For our expressions,
the main things we are going to need are:

1. Numeric literals (arbitrary precision, for now) - `23`, `-1`, `2`.
2. Let-bindings - `let <pattern> = <expr> in <expr>`. The pattern in the let
   binding will either be a variable pattern, a tuple pattern, or a numeric
   literal.
3. Arithmetic - `3 + w`, `x * z`.
4. Unchecked calls, like our `unsafe_div` function.
