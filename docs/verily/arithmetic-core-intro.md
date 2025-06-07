A high-level overview of the language core for circuits we're working with, and
some vague hand-waving in the direction of how we might go about reducing
high-level programs to that core.

## Starting out with simple arithmetic and transcripts

Let's begin with language features that correspond directly to arithmetic
circuits, as these have a variety of verification schemes in the literature
already. With only "deterministic" input, this would be a program that looks
like

```
fun main x y =
  let i = x + y in
  let j = x - y in
  i * j
```

The single top-level `main` function receives inputs (field elements) and can
evaluate expressions involving addition, multiplication, field constants, let
bindings. Correctly executing this `main` program is the same as finding a
solution to a system of equations on the variables referenced in the function
(with a single `ret` variable for the output, for this particular function)

```
i - x - y = 0
j - x + y = 0
ret - i * j = 0
```

Depending on the system, there might also need to be dynamic constraints to the
effect that the input and output variables actually had the concrete values we
expected them to have. That is, if we wanted to verify that `8 = main 4 3` we'd
want to add that `x - 4 = 0`, `y - 3 = 0` and `ret - 8 = 0`. This can be
accomplished in a way that's internal our high-level language by baking the
specific inputs we want to use and outputs we claim to produce into the function
itself:

```
fun main () =
  let x = 4 in
  let y = 3 in
  let i = x + y in
  let j = x - y in
  let ret = i * j in
  let 8 = ret in
  ()
```

That last `let` is intended to express the constraint that the return value of
this function is `8` with pattern-matching syntax; other syntax is possible.
Since the output has been added to `main` as well, we can just return `()` at
the end. This would be a pass in the compiler itself, of course, and
implementing it too naively would complicate other transformations - as written,
that entire `main` reduces to just `fun main () = () `. (Maybe you could think
of this as adding a side-effect to expression evaluation? Computing `let x = 4
in ...` has the "side-effect" of incurring a constraint that needs to be proved,
so `x` remains runtime-relevant and can't be erased.)

The collection of runtime values that are bound to the variables is the
*transcript* of the execution of this program. The constraints are there to
provide some standard to judge whether or not the transcript is actually
correct.

Once you've harvested all the constraints implied by a function (with or without
actual inputs or outputs), you can turn them into an R1CS instance and then
apply some kind of polynomial IOP or linear PCP or whatever to get a SNARK
version of your program. (TODO: list the very, very many ways this can be done -
this choice influences a lot of the compiler, as certain transformations will be
more or less efficient depending on what is chosen. But, basically you turn your
constraints into very specific polynomials that are amenable to random equality
checking. Probably should go down into another section).

## Adding more language features

You can reduce pretty complex programs to this simple core, though the result
might not be the most efficient. (N.B. this is all call-by-value - maybe you
could do verifiable graph reduction and do call-by-need, somehow.)

1. Non-recursive top-level function definitions beyond the `main` function can
   be supported. At worst (and this can be pretty bad) you can inline absolutely
   everything into `main`.
2. Complex expressions with sub-expressions can be turned into a bunch of
   intermediate `let` bindings, so the arguments to functions or built-in
   operators are always literals or variables.
3. Not exactly an extension (because circuits generally allow this), but you can
   have your functions return tuples of values. These would be consumed via
   pattern-matching.
4. Loops of fixed size are possible, but you might have to unroll the loop
   completely.
5. You can support "branching", except that you have to evaluate both branches.
   (This can also be exceptionally inefficient, especially if your program
   branches a lot). This would take `let x = if b then y else z in` and turning
   it into
   
   ```haskell
   let 0 = b * (b - 1) in -- need to make sure that b is 0 or 1!
   let x = b * y + (b - 1) * z in -- y, z might be complex expressions themselves
   ```

## What about non-determinism?

On some level (not necessarily the surface language), we'll need explicit,
unverified inputs to functions, or computations within functions. These *could*
be omitted from the function inputs entirely and simply called into existence
with some keyword - we might have gone this route if we were implementing some
kind of logic programming language. We will not be doing that - in fact, we'll
generally want to specify exactly how these inputs will really be computed! It's
just that the way they're computed might not be very easy to specify in our
simple arithmetic core, so we might prefer to arrive at values for these
variables in unverifiable ways, and then provide enough constraints on the
variable to be sure that they're what we think they are.

The usual example of this is field division, where

```
fun main x =
  let y = x / 3 in
  y + 1
```

becomes something like

```
fun main x =
  let y = unchecked_div x 3 in
  let 0 = x - y * 3 in
  y + 1
```

You've told the executor of the program that `y` should be `x / 3` (division in
the field sense!), but then, since you don't trust the executor, you immediately
assert that `y` does in fact have the value it ought to have.

"Foreign function calls" can be implemented in this way, but you do have to
arrange for there to be enough data lying around to actually verify that their
outputs match their inputs. Division is an example where the output is
constrained by the input through a simple arithmetic relation, but that's not
always the case! The most meta example here is verifiably verifying proofs. You
can have the higher-level program you want:

```
fun main x =
  let y = f x in
  y + 1
```

with `f` some function you don't want to (or can't) inline, and turn that into

```
fun main x =
  let (y, proof) = unchecked_verifiable_f x in
  let () = verify_f x y proof in
  y + 1
```

where `unchecked_verifiable_f` is a function that computes `y = f x` but also
returns an additional `proof` value. The important part is that there needs to
be a `verify_f` function *expressible in our arithmetic core* such that running
it verifiably (i.e., so its constraints get added to `main` and proved at
runtime) convinces us of the fact that `y` is in fact `f x`, even if we didn't
"see" the untrusted executor actually run `f`.

One problem with this kind of foreign call (I've heard) is that it can still
result in huge circuits very quickly, as the `verify_f` function might be really
big itself. Since every (checked) function call is inlined in our core, this can
get out of hand quite quickly, especially with multiple calls and nested
inlining.

There is also the question of syntax. In some FFI scenario, I guess you might
have something like (in pseudo-Haskell FFI syntax, but I'm not at all married to
this idea)

```
foreign import "<callingConvention>" "<funcname>" <function signature>
```

You'd want to come up with some kind of notion of safety. Rust comes to mind
here - maybe the resulting thing is only callable in the scope of an explicit
`unsafe(...)` expression? Maybe such an expression would encourage/force you to
provide post-conditions on the `(input, output)` pair returned by the foreign
function. (These could be trivial conditions - you might actually want them to
be trivial if the structure of the surrounding computation somehow provides the
invariants you want).

Now that I think about it, this really doesn't belong in the core! Unchecked
*inputs* do, but I think it will be best to start with pure circuits (or
anything that can be represented as a pure circuit). The core can be used as
glue in other components of a language - we could even have unchecked calls in
this very compiler, in fact. It would just be a separate thing from the circuit
core. Doing it that way *does* mean that we need to have good coordination
between the core representation of circuits and the other parts of the
language(s) relying on this, but would be true regardless.

(I may reconsider that decision if I find there is a good way of generating a
proof for the execution of a pure circuit without keeping the transcript around.
That does exist with folding schemes, but like I said, even those ultimately
seem to need a bootstrap non-folding proof system as glue.)

## Why restrict ourselves to such a simple core?

Branchless arithmetic is the easiest kind of computation to make
(zero-knowledge, succinct, etc. etc.) verifiable directly. It's also the
foundation of more complex cores that allow for richer language constructs to be
represented directly. So, we'd probably have to be able to restrict ourselves to
this core anyway, just to provide some bootstrap verifiability for other parts
of the compiler.

## But what are numbers anyway? Maybe we need to know?

Our core is designed to be simple and fairly reflective of the demands of
arithmetic-circuit-based proof systems. However, all of these proof systems can
use different fields! (Or just rings, or modules, in the case of lattice-based
proof systems). A circuit written entirely in the core arithmetic above is
completely polymorphic in the choice of field, sure, but a lot of proof systems
rely on the relationships between two or more fields (and/or whatever groups are
associated to them). So - do we need to add this to the core?

No. The "native language" of these arguments is arthmetic circuits in a single
field (or ring - I might try the rings/modules approach for the core). In the
literature, operations involving other rings are usually *simulated* with the
native ring, or given as a foreign function call, or as the result of a lookup.
All of that is ultimately squeezed down into circuits on a fixed field.

Now, we likely do want multiple fields to be expressible in a higher-level
language. We'll want to be able to instantiate our core on multiple fields
within the same program for that reason. (This would be in a level lower than
the surface language). There would then be a compiler pass to unify all the
fields into one using simulated field operations (or whatever we choose).

In the surface language, this might look like a built-in "platform/native"
field/ring, and then packages providing other numeric types, like a paired field
(if the platform field is the base field of one pair of a cycle of elliptic
curves). You'd obviously want a decent type system to go with this.
