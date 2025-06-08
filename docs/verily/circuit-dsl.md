## Circuit overview

Remember that a circuit, in theory, has this kind of interface:

```rust
fn circuit(detInputs: [Field; M], nondetInputs: [Field; N]) -> [Field; O];
```

You specify your deterministic inputs, magic into existence some
non-determinstic inputs, then do a bunch of arithmetic on all that to calculate
some intermediate results and eventually arrive at a final output. That's the
point of view of actual circuit execution - circuits are after all just a
computer program built out of a bunch of field arithmetic and binding
intermediate results to variables.

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

## So what does a circuit builder need to do?

What we need to give to the prover is:

1. The execution log of the circuit - this is a vector of field elements
   containing all of the values we computed for the variables in our circuit.
2. A description of the relationships between the variables we would like to
   prove are true for this particular execution log. These relationships are all
   assertions that some (very simple) arithmetic expression involving the
   variables in the transcript is equal to zero.
3. A labelling of the variables as "public" or "private"
   ("deterministic"/"non-deterministic" if you like) for the purposes of the
   proof we generate.

So what must our circuit builder allow us to do?

1. We have to be able to register new variables. These variables will have a
   symbolic component that can be referenced in constraints. Since the circuit
   execution must be decoupled from the constraint creation - we want to be able
   to harvest the circuit description from our builder before runtime - we also
   have to specify how the variable is going to get its value at runtime so we
   can fill in the execution log properly.
2. We have to be able to register simple arithmetic constraints between
   variables.
3. We have to be able to mark which variables are public and which are private.

## Squeezing a large program into a circuit

(TODO: now go into representing data operations on data as bundles of field
elements, checked/unchecked calls, that sort of thing).
