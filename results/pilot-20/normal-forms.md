# L-meta-1482: safe-wire transformations and the remaining obstacle

Status: mathematical notes, not a Lean-checked circuit-transformation theorem.
The checked 65-gate boundary circuit and its exact semantics/certificates are separate
artifacts. They do not refute the posted 64-gate statement.

## Model and terminology

Fix a finite, topologically ordered circuit over binary AND and OR. Every gate has
two distinct earlier input wires; the output is an existing wire. Its Boolean
function on all input assignments is f. No constants or NOT gates are available.
A wire H is **safe** if its Boolean function is pointwise below f:

    H(x) = true implies f(x) = true, for every complete input assignment x.

Safety must hold on all assignments. Truth only on graph-edge assignments, or
falsity on all nonedge pairs, does not establish safety: a wire can accept a larger
independent set without accepting any singleton or pair inside that set.

A circuit is **ordinary minimum** if it has least size among all legal monotone
circuits computing f. This is different from least size among circuits computing f
and satisfying the extra double-re-read condition. The moves below preserve f,
but need not preserve either formal linear recurrence or the double-re-read
condition. Thus ordinary minimality cannot be assumed for a witness to the posted
existential without a separate argument.

## 1. An AND gate with a safe operand can be deleted

Suppose gate g computes H AND B, where H is safe. Redirect all reads of g, including
the output if needed, to H, and delete g. Keep the rest of the gates unchanged
apart from index renaming and the duplicate-parent repairs described below.

For an assignment on which H is false, old g and its replacement are both false,
so the output is unchanged. On an assignment on which H is true, safety says the
old output f is true. Replacing H AND B by H can only increase a wire value;
monotonicity of all downstream gates implies the new output is still true.
Therefore the new circuit computes exactly f and uses at least one fewer gate.

Consequently an ordinary minimum monotone circuit has no AND gate with a safe
operand. This conclusion does not hold merely from minimality subject to the
extra double-re-read property, because deleting the gate may destroy that property.

## 2. Extracting a safe wire from all its downstream uses

Keep the entire prefix through H, including every other prefix wire. In the
remaining circuit, replace reads of H by a symbolic false value. Let f0 be the
resulting output. If H itself is the designated output, replace that output
occurrence by symbolic false as well, so f0 is false and the final output is H.
Other prefix wires keep their original Boolean functions even
if they share inputs or gates with H. Only occurrences of the wire H itself are
replaced; this is a circuit cofactor, not a restriction of an original input.

Monotonicity gives f0 <= f. If H is false then f0 = f, because the replacement
changes no wire value. If H is true then safety gives f = true. Hence on all
assignments:

    f = H OR f0.

Suppose k distinct later gates read H directly. Each such gate disappears when
cofactoring: AND(H,B) becomes symbolic false and OR(H,B) becomes the simplified
other operand B. The operands were distinct, so H occurs at most once in each
such gate. Recursively simplify false operands and repeated parents throughout
the suffix. Append at most one final OR gate computing H OR f0.

This gives a legal circuit of size at most size(C) - k + 1. In particular, a safe
gate wire with at least two distinct readers yields a circuit at least one gate
smaller. Extra savings may come from recursive simplification, dead gates, a false
cofactored output, or a final OR whose parents coincide.

This construction does not add a constant gate. Represent every simplified wire
as either symbolic false or an existing retained wire. The rules are
AND(false,B)=false, OR(false,B)=B, and op(B,B)=B for op=AND or OR. If the final
cofactored output is false, output H directly. A nonconstant retained output is
an existing wire, so the final OR is legal after the duplicate-parent check.

The construction keeps H and its needed prefix available for the final OR. It
does not delete H while also relying on its computation. Any discarded suffix
gate can only have readers later in the order, so processing the suffix in order
is well-founded. Keeping additional dead prefix gates only weakens the bound;
ordinary dead-gate elimination can remove them afterwards.

Thus an ordinary minimum monotone circuit cannot have a safe internal gate with
two distinct gate readers. A safe wire with exactly one reader can be extracted
without increasing size. These statements alone do not imply that every internal
wire is safe or that the whole circuit has a single AND layer.

## 3. One safe OR occurrence can be lifted, preserving size

Suppose g = B OR H and H is safe. Delete g and redirect its readers to B. Call the
resulting output f1. Append a final OR gate H OR f1, retaining H and its prefix.
Because the original gate value is decreased, f1 <= f. On H=false, g=B, so f1=f.
On H=true, safety gives f=true. Therefore H OR f1=f. One deletion and at most one
addition do not increase gate count.

This local move is weaker than the cofactor move in Section 2: other uses of H
remain unchanged. It is useful for moving a safe contribution toward the output.
A proof that repeated moves terminate in any desired global normal form needs an
explicit potential and a precise normal-form statement. No such complete
normalization theorem for arbitrary monotone circuits is established here.

## 4. Index, acyclicity, and distinct-parent repairs

All redirects in Sections 1 and 3 replace a deleted gate by one of its earlier
parents. After a deletion, compress the remaining gate indices in their original
order. The redirected wire is still earlier than every former reader, and
compression preserves the order of all retained wires. No cycle is introduced.

A redirect may turn a later gate op(A,B) into op(A,A). Such a gate is illegal for
the posted distinct-parent convention, but both Boolean operations satisfy
op(A,A)=A. Delete it, redirect to the earlier A, and continue forward. Every such
repair removes a gate and preserves the computed function. Repeating at most the
original number of gates terminates. The same check applies to the final OR.

For the cofactor construction, build a fresh suffix in topological order using
only earlier retained wires or symbolic false. Gate omissions do not require any
new signal. This simultaneously handles index compression and propagating false
values. It never increases the number of gates beyond the count above.

These repairs preserve the Boolean function, not the syntactic formal derivatives.
Repeated operands and reconverging paths matter to the latter, so Boolean
idempotence is not a proof that a derivative certificate survives a repair.

## 5. Concrete relevance of the 65-gate circuit

For the order-3 plane let r be point 2. Let F be the incidence function with point
r disabled, and let N be the OR of the four lines incident with r. The checked
boundary circuit computes

    (F OR x_r) AND (F OR N) = F OR (x_r AND N).

It has 65 gates: F uses 59, N uses 3, and the displayed outer factorization uses
3. It has 13 AND gates and 52 OR gates. At the chosen edge (point 0,line 0), point 0
differs from pivot point 2 and line 0 is not in the neighbor set of point 2. Both
formal linear parts at the output vanish; the exact finite certificates were Lean
checked.

The wire F is safe and has two readers. Section 2 removes those two readers and
adds at most one OR, yielding the ordinary 64-gate form on the right (13 AND and
51 OR gates). The extra double-re-read condition is lost. Thus it is unsound to
apply ordinary-minimum normalization while silently retaining that condition.

The example also refutes an attempted intermediate assertion that every
double-re-read circuit needs at least 14 AND gates. It has only 13. A possible
tradeoff such as at least 14 AND gates OR at least 52 OR gates remains unproved.

## 6. Why the first-loss witness does not finish the lower bound

The checked first-loss helper extracts an AND gate where, on a chosen incidence
pair, both parents are true; on the relevant singleton, both parents are false;
and their incoming linear values are true while the AND output loses linearity.
This is a local statement about evaluations at a few assignments. It does not
show that either parent is safe on all assignments. Therefore Sections 1-3 cannot
be applied merely from the existence of this witness.

At any safe AND gate A AND B, let S_A and S_B be the sets of variables that make A
and B true on singleton assignments. The sets are disjoint because f rejects
singletons. Any distinct a in S_A and b in S_B must form a graph edge: monotonicity
makes both operands true on {a,b}, and safety then makes f true there. For a
C4-free bipartite graph, if both supports are nonempty, their cross rectangle is
therefore a star; one side has size at most one. This is a valid local restriction.

It does not account for an edge accepted by already mixed terms in both operands,
including the case where both singleton supports are empty. More generally, an
unsafe intermediate OR/AND family can accept nonedges or larger independent
sets that a later AND filters out. The final graph being C4-free does not make
all intermediate rectangles safe. Even a globally safe wire need not be quadratic:
a term xyz is safe whenever xy is an edge, but its own minimal term can have
three variables. Extracting safe wires therefore does not automatically extract
edge-disjunction components at unchanged cost. The missing proof is a resource inequality
charging these filtering and repeated mixed-term effects, with enough precision
to exclude size 64 when both linear parts vanish on one edge.

No ordinary lower bound of 64 for all monotone circuits is proved by these notes,
and no proof is given that a double-re-read circuit can be reduced while retaining
its extra condition. These are exactly the logical gaps that prevent completion.

## 7. Existing repository support and its limits

The following source files were inspected in the current checkout:

* lean/PEqualNP/Defs/CircuitMoves.lean defines eraseRedirect, eraseGate,
  WireBelowOutput, liftAt, Lift, and JunkDrop. These are syntactic move definitions;
  the module does not prove the needed semantic or size-minimality theorem.
  In particular JunkDrop alone has no semantic-preservation hypothesis.
* lean/PEqualNP/MetaComplexity/Helpers/EdgeFnModel.lean proves redirect/delete
  facts rdel_length, rdel_clean, rdel_prefix, and rdel_all. The last requires that
  the deleted gate equals its replacement at the assignment under consideration.
* lean/PEqualNP/MetaComplexity/Helpers/EdgeFnLift.lean proves stmtLift, the safe-OR
  lift of Section 3 in the existing Readers.Least framework, and a tail-potential
  increase under its additional hypotheses. This is an actual checked theorem,
  not merely a plan statement.
* EdgeFnPlan.lean lines 55-62 gives its precise StmtLift proposition. It assumes
  Readers.Least for the function and nonconstancy. Readers.lean lines 58-62
  minimizes over all CleanL gate lists computing the function.
* Parity3.lean lines 28-34 defines CleanGate/CleanL. This permits unary NOT and
  binary AND/OR and does not require the two binary parents to be distinct.
  Therefore these existing hypotheses are not literally the posted restricted
  monotone/distinct-parent minimality hypotheses. The repairs in Section 4 would
  still have to be connected to the posted model.
* EdgeFnXMove.stmtXMove explicitly appends NOT and OR after deleting two AND
  readers. It cannot serve as a monotone-only size transformation unchanged.
* EdgeFnAnd.stmtAnd replaces an AND partner by NOT of an input and proves a
  restriction gate-saving statement. It likewise is not the missing monotone
  normal-form or double-re-read lower bound.

A bounded filename/content search found no TopForm helper in the searched Defs,
MetaComplexity, and Outside paths. This is not a claim about an absent future
module or any external branch.

The posted single-file/import rules also mean these helper modules cannot simply
be added as new arbitrary imports to the submitted proof. Any adaptation must
respect the allowed import closure and reproduce the needed proof within the
named file if necessary.
