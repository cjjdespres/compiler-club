---
series: |
  Verifiability and the essence of composition
title: |
  Part 1 - a light overview
status: |
  draft
---

# Where are we going?

Our goal in this series will be to explore the "verifiability problem", which
I'll phrase as:

> Given a computer program, can we find an equivalent program that returns the
> same result, but also provides a proof that the result was computed correctly?

These kinds of transformations allow you to offload the actual work of running a
program onto other parties that you do not necessarily trust: just have them
execute the verifiable version of the original program and send back both the
result and the proof of correctness for you to verify. As we shall see in later
articles, they also permit you to write new kinds of programs that are
impossible to write without having access to this kind of verifiability.

Of course, any program can be made verifiable, by having the verifiable version
save the entire execution history of the original as a proof of correctness.
You'd then verify the proof by running through each step in the execution to
make sure it was computed correctly. This scheme definitely works, as long as
you don't care about the cost! That kind of proof will be huge for any
non-trivial program, and will take as much time to verify as just executing the
original. The difficulty in the verifiability problem is coming up with systems
that do better. Ideally, our verifiable programs will:

1. Produce proofs of correctness that are small and do not take a lot of
   resources to verify
2. Run while taking time and space that's as close as we can get to the
   non-verifiable originals

We will achieve this, but at the cost of a very small amount of certainty in our
proofs---they will be generated according to (pseudo-)random processes and will
have a very low, but non-zero rate of false positives. The exact places where
randomness comes in will be omitted until we get into the details of specific
systems.[^randomness]

[^randomness]:
    These proofs are usually first presented as if they depended on truly random
    parameters, and then that randomness is replaced by what is effectively a
    pseudo-random number generator with initial seed derived from the
    cryptographic hash of a bunch of the data on hand.

As we talk about different systems, we will gradually expand the number of
language constructs that our programs are allowed to use and still be eligible
to be made verifiable. We will also fill in the details over time, eventually
getting to concrete implementation details and actual cost estimates for our
programs. Finally, a lot of these transformations will be presented as if we
were writing them by hand, but we will eventually get to ways of automating all
of this as well.

# The basic verifiable interface

Our base programs will be presented as normal Rust functions

```rust
fn f(inp: Input) -> Output;
```

taking some number of input parameters and returning some `Output`. Their
verifiable representations will look like

```rust
fn vbl_f(inp: Input) -> (Output, Prf_f);
fn chk_f(inp: Input, out: Output, pi: Prf_f) -> bool;
```

For `(out, pi) = vbl_f(in)`, the `pi : Prf_f` will be some representation of a
proof of a statement, usually something to the effect that `out ==
f(in)`.[^caveat-on-proof] These verifiable representations will come with a
`chk_f` function that verifies whether or not the proof is correct. In the
scenarios we talk about, we'll be calling the party that's responsible for
running the (verifiable) functions the "Prover", and the party that's
responsible for checking the proof the "Verifier".

[^caveat-on-proof]:
    This will be true at the beginning, but we're about to encounter verifiable
    functions that must necessarily produce more subtle statements about their
    output and execution

As a little preview of the difficulties to come, I'll note here that we won't be
able to prove exactly the statements we want to prove, at least not directly.
The systems we talk about will only really be able to prove that a bunch of
arithmetic on numbers is equal to a different bunch of arithmetic on
numbers.[^what-numbers] We're going to have to work hard to show that the
statements we want to prove have equivalents in these systems. With that in
mind, here is a list of language constructs that we can use in a function and
still be able to find a verifiable representation for it, ranked according to
how bad we should feel if we invoke them without explaining the techniques we're
using to make them verifiable:

[^what-numbers]:
    The question "what kind of numbers?" will also become very important

1. Basic arithmetic on numbers: a statement that this was done correctly is
   exactly the kind of thing our systems can work with
2. Saving intermediate arithmetic results in variables: ditto
3. Operations on tuples of numbers: as long the tuples aren't too first-class,
   this reduces to operations on a bunch of numbers
4. The `==` operation on numbers, returning the number `1` if equal and `0` if
   not: this can be encoded with arithmetic, at the very least
5. Conditional expressions if you don't care about evaluating both branches of
   the conditional: e.g., `if b then x else y` for numbers `x` and `y` can
   become `b * x + (1 - b) * y`
6. Enums, records, match statements on these: can all be encoded as tuples of
   numbers and conditional statements
7. Non-recursive calls to known functions: inline the function
7. Loops of a fixed size and recursion of a fixed depth: just unroll the loops
8. Unknown function calls, loops of dynamic size, recursion of dynamic depth,
   data types not easily expressible as a static amount of numbers: this will
   take a *lot* of work

We'll be trying to find better ways of finding verifiable representations of
functions as well, so we don't have such a contorted final computation; we'd
rather not evaluate both branches of all our conditionals, for instance, or be
forced to unroll all our loops or inline all our functions.

# Adding non-determinism to our interface

Logic programming languages like Prolog have a particular notion of
*non-determinism* that they like to use, one that will be convenient for us to
add to the model of verifiable computing that we are developing. This kind of
non-determinism is not necessarily related to randomness; instead, it expresses
the demand we might make at certain points in a computation that a value be
given to us from some outside source, rather than be computed by us.[^on-logic]

[^on-logic]:
    In logic programming languages, these values might be the result of a search
    query whose implementation is built in to the language, or at least not
    locally specified by the programmer.

In our systems, non-determinism will be modelled by having our functions take
two flavours of input: deterministic, and non-deterministic. These labels won't
affect our base functions at all. Instead, they will change who is responsible
for providing the inputs to the verifiable versions of our functions.
Deterministic inputs will be our responsibility to provide, and
non-deterministic inputs will be Prover's responsibility. (Recall that Prover is
the party that will be running the functions). These labels will also affect the
statement that the proof represents, as we shall see at the end of this next
example.

So, suppose you had a function that factorizes numbers:

```rust
fn factor(x: u64) -> u64 {
  // If x is 0, 1, or prime, output 1
  // Otherwise output a factor of x other than x or 1.
}
```

You might have writen a unit test for it as well:

```rust
fn test() -> Result<(),()> {
  const P: u64; // Hardcoded big prime number
  const Q: u64; // Another hardcoded big prime number
  let x = P * Q; // P, Q not too big, so this doesn't overflow
  let y = factor(x);
  if 0 == (x % y) {
    Ok(())
  } else {
    Err(())
  }
}
```

This test applies `factor` to some known number that's hard to factor. Because
it's hard, you might want to outsource this computation to Prover. Fortunately,
this `test` function will have a verifiable representation:[^justify-vbl]

```rust
fn vbl_test() -> (Result<(), ()>, Prf_test)
// We get chk_test too
```

[^justify-vbl]:
    Considering what we talked about in the previous section, we should feel
    moderately bad about this claim

This is all good, except for one small issue: we've left out the values of the
hard-coded primes `P` and `Q`! We could go through the trouble of finding
suitable primes ourselves, but we're already pretending we're very
resource-constrained, so that might be way outside our budget. Thankfully, the
power of non-determinism can save us. Not only can we avoid running the code to
find the primes, we can even avoid *writing* the code to find the primes by
rewriting our test function:

```rust
fn test_2(p: u64, q: u64) -> Result<bool, ()> {
  // Add some obviously-correct brute force check
  // to make sure that p and q are primes and
  // within the right range of sizes.
  // Abort the test if they aren't.
  if p_not_right || q_not_right {
    // Use Err(false) to indicate the failure
    // was in test setup
    return Err(false)
  }

  let x = p * q;
  let y = factor(x);
  if 0 == (x % y) {
    Ok(())
  } else {
    // Test failure, not test setup failure
    Err(true)
  }
}
```

This `test_2` receives its primes as inputs, rather than hard-coding specific
values for them. These inputs will both be considered non-deterministic as well,
so it will be Prover's responsibility for providing them. That's why the very
first thing we do in the test is to check to make sure the inputs are actually
primes of the size we want---we need to prevent Prover from deceiving us with
bad test inputs. Our other modification is to the return type, because we need
to distinguish between test setup failures (caused by bad inputs) and actual
test failures (caused by our code being buggy).

If we make this function verifiable[^on-subtlety] we'll get

```rust
fn vbl_test_2(p: u64, q: u64) -> (Result<bool, ()>, Prf_test_2)
```

[^on-subtlety]:
   Just add non-determinism to the list of language constructs we should feel at
   least a little bad about using without justification

The verifiable version of `test_2` computes the output `y = test_2(p, q)` of
that function, and also outputs a proof `pi : Prf_test_2` that this result `y`
is correct. But, what does "correct" mean? It can't be that `y = test_2(p, q)`,
because we don't know what `p` and `q` are; they were generated by Prover
itself. Instead, the best we can do is the statement "there exist values `p` and
`q` for which `y = test_2(p, q)`". But this statement is enough! Once we've
established that it is true, we can look at the `y` and see how the test turned
out:

1. If `y` is `Err(false)`, then Prover tried to deceive us with bad test inputs
   and got caught[^on-reality]
2. If `y` is `Ok(())`, then the provided test inputs were okay and the test
   succeeded using them
3. If `y` is `Err(true)`, then the provided test inputs were okay and the test
   failed using them

Broadly speaking, calling an input `x: X` non-deterministic will convert the
statements our proofs establish from

> Given the specific input `x`, the value `y` is the output of your function `f`
> applied to that `x`

into

> There is some unspecified input `x` such that `y` is the output of your
> function `f` applied to that `x`

These weaker types of statements can still be useful, as the example of this
section demonstrates. It's just that we might have to add some sort of
verifiable checking to our functions, or modify their structure in other ways,
so that these statements say something that is interesting to us. For a simple
example of a less interesting result of this verifiability transformation,
consider the function

```rust
fn add(x: u64, y: u64) -> u64 {
  x + y
}
```

If we consider `x` deterministic and `y` non-deterministic, then making this
verifiable will yield

```rust
fn vbl_add(x: u64, y: u64) -> (u64, Prf_add)
```

We will be responsible for providing an `x`, and Prover will be responsible for
providing a `y`. The output will be some `z: u64`, together with a proof `pi :
Prf_add` of the statement "there exists some `y` such that `z = x + y`". This is
a pretty obvious statement! Especially since `z` is something that Prover is
also responsible for computing. It could easily set `z = x` and provide a proof
that `z = x + 0`, but there is a proof for any `z` output that Prover might
choose.
