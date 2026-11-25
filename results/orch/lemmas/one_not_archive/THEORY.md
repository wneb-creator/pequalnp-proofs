# One-NOT Petersen routes

Status: mathematical analysis, **not formalized in Lean**. Every gate-count
claim below that uses normalization or constant propagation still needs
the corresponding Lean circuit transformation.

## Endpoint constraint

For a unique NOT gate, its input function `g` is monotone. If it is
nonconstant, `g(0)=0` and `g(1)=1`. The Petersen edge function has
`F(0)=0,F(1)=1`. An all-AND path from the NOT output to the final output
would force `F(1)=0`. An all-OR path would force `F(0)=1`. Thus every
such path must contain both an AND and an OR. In particular at least two
binary gates follow a live NOT.

If exactly two binary gates follow the NOT, after removing redundant
uses the suffix has one of the forms

```
F = (NOT g AND a) OR b
F = (NOT g OR a) AND b
```

The three values `g,a,b` come from a common monotone prefix. At total
size 19 that prefix has at most 16 binary gates. This is a concrete
finite search shard; it does not settle the full one-NOT case.

## Raw-input NOT and the nine-vertex lower bound

If the NOT negates an original variable, it can be commuted to the front.
Vertex transitivity permits choosing `NOT x0`. Consider a circuit with
valid binary wiring, no unused gates, no duplicate-input identities, and
no constant gates. The raw input and its negation cannot be the two
operands of one live gate: that gate is constant and should be simplified.

Restricting `x0=0` deletes the NOT and simplifies every direct consumer
of `x0` and `NOT x0`. A four-gate saving would leave a circuit of at most
15 gates for the nine-vertex induced graph, contradicting the checked
bound in L-meta-8367.

Consequently a surviving normalized 19-gate case should have exactly one
positive consumer and exactly one negative consumer. The positive
consumer must be OR: an AND becomes zero and propagates through another
gate. The negative consumer must be AND: an OR becomes one and likewise
propagates. When a propagation reaches the other already-counted
consumer, that consumer becomes constant too and must propagate further,
because the restricted target is nonconstant. Overlapping and dead-wire
cases need to be included in the formal deletion lemma.

The residual form is therefore a 16-gate monotone circuit for the
nine-vertex graph, extended by three gates
`NOT x0`, `x0 OR h`, and `(NOT x0) AND k`. On changing `x0` from zero to
one, those two latter wires change from `h,k` to `true,false`. Classifying
which optimal 16-gate circuits admit this pair of changes is a smaller
finite problem. The existing nine-vertex certificate proves the lower
bound, not the needed optimal-form classification.

## A potentially eliminable source orbit

Suppose the live NOT negates the AND of an adjacent pair of raw inputs.
Move that AND to the first position. Its value `g` satisfies `g <= F`,
so the conditional semantic lemma permits replacing the NOT output by
true. Constant propagation then removes the NOT and at least one binary
consumer. If the first AND remains, at most 17 binary gates remain,
contradicting the proposed first-AND lower bound of 18. If the first AND
also becomes unused, at most 16 binary gates remain, contradicting the
global lower bound of 17. The first AND precedes the NOT, so its deletion
is distinct from deletion of a NOT consumer.

This route depends on the first-AND lower bound and formal constant
propagation, and applies to a live NOT. A circuit containing an unused
NOT reduces to a monotone circuit of size at most 18, which is a separate
case; it cannot simply be dropped from the posted statement.

Do not use a general same-size NOT-elimination claim. The full Petersen
monotone minimum of 20 is not established by the known 20-gate example;
the corresponding lower-bound step L-meta-2590 remains open.
