---
series: |
  Verifiability and the essence of composition
title: |
  Part 1 - a light overview
status: |
  draft
---

:::abstract

> In this and subsequent articles, I will be elaborating different types of
> proof systems. For our purposes, proof systems are algorithms that can be used
> to produce convincing arguments, checkable automatically, that certain
> statements are true. These statements will typically be assertions that
> certain computations were performed correctly, and for reasons of efficiency
> the arguments will be probabilistic, so our checking procedures will have
> (very, very tiny) rates of false positives and negatives. My focus will be on
> those systems related to folding schemes; that subject is new, under heavy
> research, and depends on a lot of prior work in the field, so I have been
> finding it difficult to understand them in all their minute detail. I hope
> that writing these articles will clarify at least my own thinking on the
> subject.
>
> This first article sketches some of the things these proof systems can do,
> without getting into how they do them. My intent is to provide a good, if
> vague, overview of the different components of these systems, without
> distracting implementation details. Subsequent articles will work through
> these details.

:::

# Basic verifiability

Let's begin with the sketch of a function in Rust,

```rust
fn factor(x: u64) -> u64 {
  // If x is 0, 1, or prime, output 1
  // Otherwise output a factor of x other than x or 1.
}
```

This is a normal function that computes a particular factor `y: u64` of its `x:
u64` input. It might take a while to evaluate, though, on certain outputs. It
would be nice to have the option to send a description of this function `f` and
an input `x` to another party and have them compute the result `y = factor(x)`
for us. It would be even nicer if we could do that even if the other party is
intent on deceiving us. Who knows---maybe the only people around with free
server capacity happen also to be exceptionally evil? To be consistent with the
established terminology of the field, we will call this (potentially evil) other
party Prover.

To give us the option to offload our work onto Prover, we would like to augment
our function, turning it into

```rust
fn ver_factor(x: u64) -> (u64, Prf_factor)
```

This function will compute `y = factor(x)`, and in addition will output a value
`pi : Prf_factor`. This `pi` will be a proof, or at least a very convincing
argument, that the value `y` is indeed the value of `factor(x)`. We can send
*this* function to Prover, and then use the `pi` we get along with the `y` to
establish the validity of `y` to our satisfaction. We will end up demanding that
these proofs satisfy a variety of properties as we continue; for now, let's just
keep in mind that ideally these proofs will be cheap to construct, cheap to
verify, and cheap to send across the wire. We will also leave the specifics of
what kind of functions can be made verifiable in this way, how they can be made
verifiable, or the efficiency of any of this until a later article.[^on-apology]

# Adding non-determinism

Logic programming languages like Prolog have a particular notion of
*non-determinism* that they like to use, one that will be convenient for us to
add to the model of verifiable computing that we are developing. This kind of
non-determinism is not necessarily related to randomness; instead, it expresses
the demand we might make at certain points in a computation that a value be
given to us from some outside source, rather than be computed by us.[^on-logic]

In our systems, non-determinism will be modelled by having our functions take
two flavours of input: deterministic, and non-deterministic. These labels won't
affect our base functions at all. Instead, they will change who is responsible
for providing the inputs to the verifiable versions of our functions.
Deterministic inputs will be our responsibility to provide, and
non-deterministic inputs will be Prover's responsibility. These labels will also
affect the statement that the proof represents, as we shall see at the end of
this next example.

So, to give that example, suppose you wanted to test your `factor`
implementation from the previous section, and you wanted to offload even this
test computation to Prover. You might start with the following unit test

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

This test, which runs `factor` on a number that might be difficult to factor,
has one small issue: we've left out the values of our hardcoded test constants
`P` and `Q`. We could go through the trouble of finding these primes ourselves,
but since we're already avoiding running the test, why not avoid finding the
primes too? Even better: we'll use non-determinism to avoid even having to write
the code to find them! To that end, consider instead the function

```rust
fn test'(p: u64, q: u64) -> Result<bool, ()> {
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

This `test'` receives its primes as inputs, rather than hard-coding specific
values for them. These inputs will both be considered non-deterministic as well,
so it will be Prover's responsibility for providing them. That's why the very
first thing we do in the test is to check to make sure the inputs are actually
primes of the size we want---we need to prevent Prover from deceiving us with
bad test inputs. Our other modification is to the return type, because we need
to distinguish between test setup failures (caused by bad inputs) and actual
test failures (caused by our code being buggy).

If we (somehow) make this function verifiable[^on-subtlety] we'll get

```rust
fn ver_test'(p: u64, q: u64) -> (Result<bool, ()>, Prf_test)
```

The verifiable version of `test'` computes the output `y = test'(p, q)` of that
function, and also outputs a proof `pi : Prf_test` that this result `y` is
correct. But, what does "correct" mean? In the previous section we said that the
`pi: Prf_factor` would establish that `y = factor(x)`. Here, we never see inputs
`p` and `q`, so we can hardly say that the statement is that `y = test(p, q)`.
Instead, the best we can do is the statement "there exist values `p` and `q` for
which `y = test'(p, q)`". But this statement is enough! Once we've established
that it is true, we can look at the `y` and see how the test turned out:

1. If `y` is `Err(false)`, then Prover tried to deceive us with bad test inputs
   and got caught[^on-reality]
2. If `y` is `Ok(())`, then the provided test inputs were okay and the test
   succeeded using them
3. If `y` is `Err(true)`, then the provided test inputs were okay and the test
   failed using them

In general, calling an input `x: X` non-deterministic will convert the
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
fn ver_add(x: u64, y: u64) -> (u64, Prf_add)
```

We will be responsible for providing an `x`, and Prover will be responsible for
providing a `y`. The output will be some `z: u64`, together with a proof `pi :
Prf_add` of the statement "there exists some `y` such that `z = x + y`". This is
a pretty obvious statement! Especially since `z` is something that Prover is
also responsible for computing. It could easily set `z = x` and provide a proof
that `z = x + 0`, but there is a proof for any `z` output that Prover might
choose.

[^on-apology]:
    To look ahead a little, it will turn out that we can make any function
    verifiable in this way, more or less, but functions that do a lot of
    specific kinds of arithmetic will be especially easy to make verifiable.

[^on-logic]:
    In logic programming languages, these values might be the result of a search
    query whose implementation is built in to the language, or at least not
    locally specified by the programmer.

[^on-subtlety]:
    As a preview of what's to come, I should point out that the body of `test'`
    contains a call to a function `factor`, is able to return early, evaluates
    conditional statements, and also returns a complex data type and not just a
    number. It will actually take quite a bit of work to establish that
    functions that do more than basic arithmetic can be made verifiable. I'll
    hand-wave these concerns for now by saying that we can just inline
    everything into `test'`, eliminate the conditionals at the cost of
    potentially doing extra work, and have the test result be encoded as the
    numbers `0`, `1`, or `2`.

[^on-reality]:
    This case is unlikely to occur in practice: a Prover that actually wanted to
    deceive us would just decline to execute `ver_test'` entirely, or would
    resign itself to the task and execute `vest_test'` correctly. Regardless,
    this check must still be present in order to prevent any hypothetical
    deception.
