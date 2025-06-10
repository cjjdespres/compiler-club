## Circuit overview

Remember that a pure circuit, in theory, has this kind of interface:

```rust
fn circuit(detInputs: [Field; M], nondetInputs: [Field; N]) -> [Field; O];
```

You specify your deterministic inputs, magic into existence some
non-determinstic inputs, then do a bunch of arithmetic on all that to calculate
some intermediate results and eventually arrive at a final output. That's the
point of view of actual circuit execution - circuits are after all just a
computer program built out of a bunch of field arithmetic and binding
intermediate results to variables.

N.B. "non-deterministic" just means "an exact value for this variable does not
appear in the final proof". For the circuit above, the proof that gets generated
for the computation `y = circuit(x, w)` would say "for the given `x` and `y`
there exists a `w` such that `y = circuit(x, w)`". You as the person requesting
that `circuit` be executed would supply an `x` and receive a `(y, proof)` back,
with `proof` being some checkable representation of that statement. You can
suggest to the executor ways of finding the value `w` (and end up doing that in
real protocols), but they're not obliged to take your advice. It's up to you to
structure the circuit so they can't cheat you!

Proof systems generally take a different view. Rather than specify *how* to
compute the variables in a program, the circuit specifies the *relationships*
that the intermediate results in a circuit must have with each other in order to
be correct. The runtime execution of the circuit is separated from the proving!
In fact, at runtime you can compute the intermediate results in the circuit
however you like. The only thing you need to do is ensure that you save those
intermediate results in a format that's consistent with the circuit description.
(Correctly format the execution log for your program, basically). The proof
generator just needs to be handed a description of the circuit and the execution
log of your program in order to work.

## Impure circuits and interfacing with a host language

We can have our "circuits" do a bit more, actually, by introducing auxiliary
input to our model. This input is data that does not relate to the circuit
structure in any way; instead, it can be fed to "unchecked calls" to functions.
Those functions are allowed to be used to determine the values of
non-deterministic inputs to the circuit! They can also transform the auxiliary
input too, of course. Again, these non-determinstic inputs should have
constraints on them so you know you're not being cheated by a dishonest
executor. (Or the structure of the circuit should give you guarantees about
their values in other ways. Whatever works.)

Putting it all together, you might think of these programs as having this kind
of interface at *runtime*

```rust
fn circuit(detInput: [Field; M], auxInput: AuxIn, transcript: &mut [Field; TSize]) -> AuxOut
```

This circuit takes in the deterministic inputs `detInput` that have already been
computed and the auxiliary input `auxInput` needed to run. It will fill in the
provided transcript slice with whatever values satisfy the circuit constraints,
and return whatever (unchecked) output you expect it to return.

(You could also have it return a `Vec<Field>` of field elements for the
transcript, or have it take a dynamically-sized slice of field elements for a
transcript. There are many options.)

At compile time, the circuit needs to have something like this interface:

```rust
fn circuit(inputs: [CircuitVar; ISize], freshVarSource: VS) -> (Vec<Constraint>, VS)
```

The circuit takes in symbolic variables for its inputs, and a source of fresh
variables (realistically - a variable index that's higher than all the existing
indices). It returns all the constraints on its intermediate variables (its
internal circuit structure) and the updated source of fresh variables (from
which you can determine how many intermediate variables it uses).

This kind of interface is convenient for "checked calls" - if you had the pure
circuit pseudo-code

```rust
fn other_circuit(x: Field) -> (Field, Field) {
  let i = x + 1;
  let j = x * 2;
  (i, j)
}

fn main(a: Field) -> Field {
   let (c, d) = other_circuit(c);
   d
}
```

then during the compilation of `main` you need to be able to inline
`other_circuit` completely - that means that we need to be able to reserve
transcript space for `other_circuit`, and we need to inline all of the
constraints from `other_circuit` into `main`. That explains the `CircuitVar`
input component - you need to make sure the inlined constraints reference the
variables the circuit is being called on - and it also explains the fresh var
source input - you need to be able to generate intermediate input variables in a
way that does overwrite already-existing variables.

Other compile-time interfaces are also possible - perhaps you enforce the
convention that when a circuit is called it will always reference the last `n`
circuit variables that have been defined. You might need to add copies of the
variables you want to use as inputs, of course, but maybe you could add an
optimization pass that removes unnecessary copies? (Note that optimization in
this kind of DSL could be tricky, depending on the design, because we need the
compiled constraints and transcript shape to be kept in sync with the actual
runtime representation of the circuit).

## The design of snarky

To review, a circuit program has two components:

1. The compile-time representation, which is a list of constraints on entries of
   a transcript (an array of field elements).
2. The runtime representation, which is a way of filling in the entries of a
   transcript with values that satisfy the constraints (in addition to doing
   whatever else you want your program to do).

and the main operations involved here are:

1. Creating new circuit variables (referencing an entry in the transcript)
2. Created constraints (referencing circuit variables)
3. Specifying how the transcript will be filled in at runtime
   
Snarky is designed so you can specify both components at once, and so that all
of the main operations can be performed independently of each other. It does
this by having circuit variables be *both* a symbolic variable (can be
referenced in constraints) *and* a mutable memory location that can be filled
with a value at runtime. You explicitly create them in your program (which also
registers them somewhere, I believe), and get some kind handler that you can
manually fill in with something that can be run to get a value for that variable
at runtime. Constraints can be added manually as well. Of course, the DSL is
designed so that the constraint adding and runtime handling is done somewhat
automatically - if you say you want variable `z` to be the field sum of `x` and
`y` then we can add the correct constraint and also the runtime filling (just
read the values of `x` and `y` from the transcript, effectively).

That design is somewhat unfortunate, in that it exposes the runtime/compile-time
distinction to the user in a kind of unsafe way - it feels like you could easily
forget to actually fill in the variables with your handler, or you might
accidentally read the (uninitialized) value of a variable at compile time. I'd
like to find a better way of going about this - I think it's possible and could
be made elegant in practice (maybe too optimistic!), and as much as possible the
circuit structure (runtime and compile time) should be specified exactly once in
any DSL design.

Though, the current o1js circuit creation API might rely heavily enough on the
really extreme decoupling that snarky provides that you're forced to do it the
snarky way?

## Getting into the circuit builder

TODO: fill in - how do we specify how transcript entries are filled, either
through checked or unchecked calls? how does the aux input get threaded around?
can we add optimization passes?

(random thought - specify a "universe" of foreign functions with a uniform
calling convention, so that a circuit compiler can generate code (in a loose
sense) to set up a call to them and run them at runtime, but also has the
freedom of optimizing the actual circuit structure, since we'd no longer be
generating functions with raw memory locations embedded in them that they expect
to read to/write from).
