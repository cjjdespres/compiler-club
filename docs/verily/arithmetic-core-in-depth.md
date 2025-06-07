With the vagueness of [the introduction to the core](./core-intro.md) out of the
way, we can get into the structure of the core a bit more. For our expressions,
the main things we are going to need are:

1. Numeric literals (arbitrary precision, for now) - `23`, `-1`, `2`.
2. Let-bindings - `let <pattern> = <expr> in <expr>`. The pattern in the let
   binding will either be a variable pattern, a tuple pattern, or a numeric
   literal.
3. Arithmetic - `3 + w`, `x * z`.

Top-level function (circuit) definitions need a name, a list of deterministic
inputs `dets` and a list of non-deterministic inputs `nonDets`. They're simple
enough that their return type can be inferred as `returnTy` (though we could
explicitly type everything during the transformation into core). We will be able
to take this core for a circuit `C` and interpret it, or compile it and execute
the result, to get:

1. A result `y : returnTy` after evaluating `C(x, w) : (dets, nonDets)`
2. Some kind of proof object representing the statement "Given `x` and `y` there
   exists a `w` such that `C(x, w) = y`"
3. Some kind of procedure to check these proofs. (This procedure ideally being
   expressible in pure circuit arithmetic, of course, for maximum compositional
   flexibility).
