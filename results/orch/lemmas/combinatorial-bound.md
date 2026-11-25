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

## Further phase: matching-to-AND injection

The proposed Hall argument remains unproved. For each accepted edge of a maximum
matching, one can consider all AND gates true on its pair input. A successful
injection into these gates would give the desired AND bound. Merely choosing
the first AND where both endpoints meet fails: the P4 filtering example in
core-charging.md creates two matched edges at one AND and needs a later AND to
remove a bad pair. Including later filters restores the necessary candidate
gates in that example, but no general Hall inequality has been established.

Looking only at independent transversals of the matching is insufficient. With
matching edges a_i b_i, a cross edge a_i b_j imposes an implication on which
endpoint is selected. A directed cycle of these implications can force all
choices equal, leaving only the all-left and all-right transversals. Additional
maximal independent sets that omit some matched pairs carry essential negative
information. This is already visible for even cycles.

Free-OR normalization offers a useful simplification. Factor common selected
wires from each AND operand using (A OR C) AND (B OR C) = C OR (A AND B), and
replace future uses accordingly. Processing gates topologically yields disjoint
operand-factor sets without increasing AND count; absorbed gates may be padded
unused. In this normalized model every AND generator rejects every singleton:
earlier generators do by induction, and the raw input sets of the two operands
are disjoint. This does not make intermediate generators below the graph
function, and filtering bad pairs and larger independent sets remains necessary.

A restricted linear-filter observation is sound. If g accepts an opposite-side
nonedge pair u,v and g AND OR(R) is below fG, every r in R must be adjacent to u
or v. Bipartition determines which endpoint. If R has at least two vertices of
each color, C4-freeness makes the endpoints of every such bad pair unique. This
explains why one shared linear filter cannot cheaply repair many unrelated
rectangles. The argument does not extend as stated to same-side bad pairs or
nonlinear filter operands.

Finite search prioritization: an exact graph function computed with k AND gates
has at most 2^k maximal false inputs, by choosing a false operand at each AND.
Brute-force maximal-independent-set counts for C6,C8,C10,C12,C14 are respectively
5,10,17,29,51 (cycle-mis-census.json). Thus counting alone forces AND counts
3,4,5 for the first three cycles, but permits five ANDs for C12 despite its cover
number six. C12 with five AND gates and free OR gates is a useful next auxiliary
test, suggested to the counterexample agent. No such counterexample is claimed.

An explicit pair-only impostor clarifies the missing Hall step. Index six
matched pairs a_U,b_U by the two-element subsets U of {1,2,3,4}. Take six OR
clauses: all a variables; all b variables; and, for each coordinate t, the a_U
with t in U together with the b_U with t not in U. Their conjunction uses five
AND gates. It accepts exactly the six matching edges among all pair inputs and
rejects the two entire bipartition classes, yet accepts the independent triple
a_{12},a_{34},b_{13}. The script pair_only_control.py verifies these assertions.
It is not a counterexample because BelowF fails.

The counterexample agent checked whether this same function could be below any
C4-free bipartite completion of its matching, obtaining UNSAT. There is also a
short combinatorial explanation: the three complementary pairs of code sets
each dominate the opposite graph part, forcing every graph vertex to have
degree at least three. Then the six right vertices contribute at least eighteen
pairs of common left neighbors, exceeding the fifteen available pairs and
forcing a four-cycle.

The analogous seven-of-ten family of two-element subsets of five coordinates
is also ruled out informally. Every graph nonneighbor set of a left code U must
share a coordinate outside U; otherwise that one left input together with all
its nonneighbors would satisfy the function. Each coordinate occurs at most
four times, forcing minimum graph degree three on 7+7 vertices. C4-freeness
then forces degree exactly three everywhere, so every U needs an outside
coordinate whose full four-code star is present. There can be at most two such
coordinates. With two, the seven codes are exactly their two stars, and their
common two-element code has neither full-star coordinate outside it. With only
one, any code containing that coordinate fails. This excludes the proposed
six-AND CNF family, but does not exclude arbitrary nested six-AND circuits.

## Direct exact-function minimization

At approximately 2026-11-25 07:41 UTC, a 900-second, one-CPU C++ heuristic began
searching for an 11-gate exact theta circuit and a 26-gate exact Fano circuit.
These are direct function searches, with no core or read-once restriction.
Each model has 128 randomized canonical minimum-cover circuits as seeds;
removing one gate and redirecting its uses gives the target gate budget.

Fitness compares all graph-edge inputs and all maximal-independent-set inputs,
18 rows for theta and 58 for Fano, using 64-bit signatures. For valid AND/OR
circuits, zero loss on these rows implies exact equality on every input.
Mutations change operations, operands and output; interchange adjacent
independent gates; or delete a gate and append another. Equal-signature merges
and neutral mutations permit movement among equivalent candidates. Simulated
annealing restarts alternate between the two graphs and use an elite pool.

The positive control removes redundancy from a 13-gate theta seed, recovers a
12-gate exact circuit, and passes an independent full 256-input truth check.
This validates discovery and verification, not the existence of a shorter
circuit. Candidate evaluation totals include duplicates and are not exhaustive
coverage. Sources, complete progress log, best genotypes, and control records
are saved under scratch/combinatorial-bound. Any zero-loss result must receive
independent full-truth validation and a Lean proof before submission.

The first heuristic phase completed its full 900 seconds with no candidate:
theta 2,236,744,869 candidate evaluations and Fano 2,236,740,000, both best
row loss one. Evaluations include repeated circuits. This is a search failure,
not a lower-bound proof. Independent complete truth replay shows the saved
bests compute exact subgraphs: theta has eight edges, cover four and eleven
active gates; Fano has twenty edges, cover seven and twenty-six active gates.
Both meet, but do not improve, their own canonical bound.

A separately reviewed final 300-second phase additionally tests accepted-pair
subgraphs H. A successful candidate must reject all original graph maximal
independent sets, have active size strictly below |E(H)| + tau(H) - 1, and
reject every H-independent assignment. Exact bipartite matching computes
tau(H); complete truth checks close the higher-degree-term loophole. This
criterion and pruning were independently reviewed, and matching was compared
with exhaustive minimum vertex covers on all 512 theta subgraphs and 256
Fano samples. Full sources, input data, controls, logs and review records are
archived in results/orch/lemmas/exact-minimize-2962.

The final 300-second phase completed normally without a candidate. Its exact
completion line is:

```text
DONE seconds=300 theta_evaluations=671904308 best=1 subtests=159023456 fullchecks=0 fano_evaluations=671880000 best=1 subtests=222575717 fullchecks=0
```

No candidate passed the strict active-gate versus cover bound. The frozen
archive includes both complete logs, summaries and a SHA-256 manifest. No
further search was run. This does not establish either the general bound or
the posted statement.
