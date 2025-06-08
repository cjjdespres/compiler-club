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

There should be an actual text format for this core. Thankfully this will be
very easy, since it's so simple. There could be lots! Mainly the text format
would be useful for examining the core that was produced during compilation
elsewhere, but it could be used for explicit test cases, or even as a language
on its own if someone were so inclined.

## Going down to R1CS

The core language can easily be transformed into R1CS constraints. That kind of
constraint on a vector `z` is given by three vectors `a`, `b`, `c` according to
the equation

```
〈a, z〉*〈b, z〉-〈c, z〉 = 0
```

A whole bunch of these can be collected into matrices `A`, `B`, and `C` (with
the vectors being rows of those matrics). That gives you the usual equation

```
Az ∘ Bz - Cz = 0
```

where `∘` is the Hadamard product of matrices.

(Usually this vector `z` is required to have an entry `1` somewhere, to exclude
the zero vector as a solution. This `1` happens to be a way of getting constant
terms into your constraints, so maybe you could think of these constraints as
being `a(z)*b(z)=c(z)` where `a`, `b`, and `c` are affine functions).
