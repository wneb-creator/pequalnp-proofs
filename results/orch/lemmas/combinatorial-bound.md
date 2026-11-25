# Single-output OR-count investigation

This is research toward L-meta-2962, not a proof of the posted statement.

## Stronger candidate

For one AO2 output h below the edge function of a bipartite C4-free graph G,
let D be the accepted graph edges. The candidate is |D| <= OR(cone(h)) + 1.
OR-combining the maximal-core outputs would imply the proposed edge-charge
component |D| <= OR(U) + mc. The candidate itself remains unproved.

By De Morgan duality, this asks for an AND-count lower bound on a monotone
function above the monotone 2-CNF of G, with the dual clauses of D surviving.
This reformulation does not remove the difficulty of reused intermediate gates.

## Exact normalization for searching with free AND gates

Order the OR gates topologically. Every operand of an OR gate is a conjunction
of input variables and earlier OR outputs after expanding only intervening AND
gates. Repeated factors can be removed by idempotence. The final output is
another such conjunction. Conversely every nonempty conjunction in this model
can be realized by binary AND gates. Thus this generator model is complete for
OR count when AND gates are free; it does not bound total gate count.

The SAT encoder in scratch/combinatorial-bound/free_and_sat.py uses this model.
It selects the factors of both operands of each OR, and the final conjunction.
Only the interchange symmetry of each OR's two factor masks is broken.
For an exact graph function it tests every graph-edge input and every maximal
independent-set input. All represented functions are monotone, so these tests
imply equality on every input. C8 with six OR gates would disprove the stronger
candidate, whose canonical OR count is seven. It would not by itself refute
L-meta-2962, because the free conjunctions may require too many AND gates.

Positive controls: a four-cycle with two OR gates, and an eight-cycle with seven
OR gates, satisfy every generated CNF clause and every full truth-table row.
The controls cover 16/256 inputs and 726/13466 clauses, respectively. The
four-cycle deliberately violates the stronger candidate when C4-freeness is
removed. These are computational checks, not Lean-checked exclusion proofs.

Result at 2026-11-25 07:06 UTC: the exact C8 instance with six OR gates returned
UNSAT (solver exit 20), within its 300-second cap. The full log and source/CNF
hashes are preserved in the scratch directory. This establishes only a finite
computational exclusion, not a Lean-checked result or the posted theorem.

The exact-graph and partial-output versions of the proposed OR lower bound are
equivalent for each fixed graph G. If h <= fG accepts edge set D, adjoining the
missing edge monomials by OR computes fG with exactly |E(G) minus D| additional
OR gates. Therefore an exact-function lower bound OR(fG) >= |E(G)| - 1 implies
OR(h) >= |D| - 1. The reverse implication is immediate by taking h = fG. AND
gates for the missing edge monomials are free in this comparison. This is an
informal mathematical reduction, not formalized in Lean.

## Why an easy pair-set invariant fails

Truncating every intermediate function to singleton and allowed-edge terms
would lose the constraints imposed by bad pairs and independent triples. In
that quotient, OR(left inputs) AND OR(right inputs) produces every allowed edge
of a projective-plane graph cheaply, because nonedges were silently deleted.
The actual circuit accepts the forbidden pairs; the quotient cannot justify
the claimed lower bound. Any invariant must retain enough information about
independent-set inputs to charge the later filters.

With at most one OR gate, expansion gives at most two terms, so there are at
most two accepted pairs. An informal two-OR analysis gives at most three
accepted pairs unless a product of two two-term sums produces a K2,2. This
small analysis is not formalized and does not extend to an established general
induction when OR outputs are reused.

## Gate-elimination route

The orchestrator proposed eliminating a bottom OR whose operand is a conjunction
of at least two distinct input variables. Dropping that branch preserves BelowF
by monotonicity. Every accepted pair lost anywhere downstream must satisfy that
whole conjunction, so at most one graph edge is lost. This is a sound informal
one-edge charge, even if the OR output is reused; it is not formalized in Lean.

The difficult remaining bottom OR is x OR y. Different later contexts can use
free AND gates to select x in some places and y in others. Replacing the shared
OR globally by either variable can then lose many distinct edges. C4-freeness
limits common neighbors of x and y, but does not directly limit these separate
neighborhoods or supply the required rewiring argument.

## Forest gate-elimination argument

The following is an informal proof strategy, independently reached by the
orchestrator and this agent. It has not been formalized in Lean; implementing
restriction, constant propagation, gate deletion, and renumbering is still
required. The argument does allow sharing inside and between cones.

OR bound: let h be any monotone circuit rejecting all singleton inputs, and let
F be a forest all of whose edges are accepted pairs of h. Then
|E(F)| <= number of OR gates + 1. For induction, take a leaf v with neighbor w.
The pair vw is accepted but the singleton w is rejected, so v is essential and
has a dependency path to the output. If F has another edge, setting v to zero
leaves a nonzero output. Consequently that path must encounter an OR gate:
an all-AND path would force h <= v. Its AND-only prefix becomes zero when v is
zero, and its first OR collapses. Constant propagation eliminates that OR,
while all other edges of F survive. Apply induction to F-v. The one-edge base
case needs no OR gate. Thus the graphic rank of the complete accepted-pair
graph is at most OR count plus one, even without a C4-free hypothesis.

AND bound: suppose additionally h <= fG for a forest G, and let D be all accepted
pairs of h. Remove isolated vertices or a leaf v whose incident edge is absent
from D by setting v to zero; this preserves D. Otherwise choose a leaf v of G
whose neighbor w satisfies vw in D. Set v to one and w to zero. A dependency
path from v must encounter an AND, because an all-OR path would make h true on
the singleton v. Its OR-only prefix becomes one, so the first AND collapses.
The remaining function h' is below the edge function of G with v,w deleted:
on an independent set of that graph, adjoining v still gives an independent
set of G once w is absent, because v was a leaf of G. Every old accepted pair
away from v,w survives by monotonicity. A minimum cover of D can contain w in
place of v, giving tau(D) = 1 + tau(D minus v,w). Induction bounds that remaining
cover by the remaining AND count, which is at least one smaller.

For several maximal cores, OR-combine their functions. This uses the gates in
their cone union once and at most mc-1 new OR gates, with no new AND gates. If
the ambient graph G is a forest, the two arguments give |D| <= OR(U)+mc and
tau(D) <= AND(U), hence the posted inequality after extending a cover of G-D.
The case mc=0 is immediate. Cyclic C4-free graphs remain outside this argument.

## Recent primary source checked

Read 2026-11-25: Krapivin, Przybocki, and Subercaseaux, Near-Optimal Encodings of
Cardinality Constraints (SAT 2026), section 3.4,
https://drops.dagstuhl.de/storage/00lipics/lipics-vol377-sat2026/html/LIPIcs.SAT.2026.23/LIPIcs.SAT.2026.23.html.
The paper gives a new monotone circuit for threshold two and shows its smallest
circuits are not single-level. Threshold two is the edge function of a complete
graph, which contains many four-cycles. This provides no C4-free counterexample.
The page does not establish the current status of superlinear lower bounds for
explicit C4-free quadratic graph functions; that status remains UNVERIFIED here.
