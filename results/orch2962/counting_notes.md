# Counting examples for L-meta-2962

The posted definition of Core.IsCore says **not both operands are implicant gates**. It permits exactly one implicant operand. The sketch's wording that both inputs are not below the function is therefore stronger than the actual definition. A core must also accept some graph edge without a read-1 proof tree. coneSet includes its root gate.

## Checked margin-one example

`CountingExamples.lean` uses K2 and the two-gate circuit g0=x0 AND x1, g1=g0 AND x0, with output g1. All graph/model/function/fixed-point hypotheses are checked by ordinary kernel decide. Gate1 is the only maximal core; its left operand is implicant and its right operand is not. D has one edge, U has two gates, mc=1, the original cover has size1 and the residual cover has size0. Thus the target inequality has left side2 and right side3: margin exactly1. The site's observed minimum margin2 is not a universal lower margin.

Compiled exit0 with empty stdout/stderr (`2962-count-examples-01.*`). SHA256:2031a5b55faebc9f62ca0f5d19d0dd7575ace1273dd1ffba766966c3df82937d.

## Checked shared dead cores

`CountingShared.lean` uses the same K2, with gates g0=x0 AND x1, g1=g0 AND x0, g2=g0 AND x1, and output g0. Both maximal cores g1 and g2 are dead. Their cones are {g0,g1} and {g0,g2}, sharing g0. They jointly accept the one graph edge. U has size3 and mc=2, so the L2962 bound has margin3.

Changing only the output to g1 makes g1 live and g2 dead; the maximal-core set is unchanged. All these statements and the lift fixed point are kernel checked. The same example disproves the stronger companion counting inequality U.card+mc≤C.size+1: it gives5≤4. This is a smaller variant of the already accepted L_meta_2969 counterexample, which uses a shared OR mask as well. It does not refute L2962.

Compiled exit0 with empty stdout/stderr (`2962-count-shared-01.*`). SHA256:224b10e1c6742b2ffea73b53e0e2cdcde94b52e330ef2cf9ff420be57494d5cc.

## Other targeted observations

Without the NoFourCycle hypothesis, K2,2 immediately violates the proposed inequality: OR the two vertices on each side, AND those two ORs, then AND the result with the first OR again. The final gate is a core; D=4edges, tau=2, U=4gates, mc=1, residualtau=0, so6≤5 fails. This boundary calculation has not been formalized here and is not a counterexample under the posted hypotheses.

A three-edge path can be written as the conjunction of its three minimal vertex-cover disjunctions, using3OR gates and2AND gates. The final gate is a nonread-1 core. Sharing such clause gadgets seems constrained by the unique-common-neighbor property: same-side OR pairs have a unique possible middle vertex. I found no violating C4-free bipartite gadget. The counterexample agent owns broader random shared-dead-core enumeration; the root owns generic cone-union/antichain lemmas.

## Exact equality, with a dead four-gate core

The counterexample agent found a stronger boundary and I kernel-checked it as `CountingTight.lean`. The graph is path0-1-2-3. Dead prefix: a=x0 AND x1, b=a OR x2, c=x1 OR x3, d=b AND c. Its output d computes the whole path function, but the edge01 has no read-1 proof tree. A separate live four-gate star-cover circuit computes the same path and supplies the actual output. The internal lift at b is dead, so the whole circuit is liftfixed.

The unique maximal core is gate3, with cone{0,1,2,3}. Its accepted edges are allthree graph edges. Minimum cover{1,2} has size2 and the residual graph has empty cover. Therefore both sides of L2962 equal5. This rules out any universal positive slack, even though the site's sampled circuits had margin at least2. It is an equality case, not a counterexample.

The complete file passed Lean with exit0 and empty stdout/stderr, archived as `2962-count-tight-01.*`.

## Checked local overlap constraints

`CountingGeometry.lean` proves: NoFourCycle gives a unique common middle vertex for two distinct endpoints; if two accepted-edge sets contain the two corresponding paths through that endpoint pair, their intersection contains at least two edges; and a bipartition forbids flipping the center of a shared-edge path gadget through the same third vertex (that would make a triangle). These are generic graph lemmas, not a complete gate-cost accounting theorem.

For the tight P4 gadget, sharing its OR(y,w) clause forces its middle z to coincide, so two accepted edges are shared. Sharing its nonhomogeneous OR(xy,z) clause forces the same xy and z; swapping x/y as center creates a forbidden triangle. This explains why the simplest gluings of exact-equality gadgets do not yield a negative margin. More general circuits remain unresolved.

The geometry file compiled with exit0 and empty `2962-count-geometry-01.*` logs.
