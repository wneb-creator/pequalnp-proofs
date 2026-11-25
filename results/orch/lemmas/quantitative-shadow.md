# Quantitative degree-two shadow review

2026-11-25 UTC. Reviewer: constructive. This is a mathematical/source review, not a Lean proof. No build, desk call, or git action was performed.

## Verdict

The proposed conclusion is mathematically sound: a circuit of at most 26 gates computing the posted Heawood function must omit at least two of the 21 squarefree degree-two edge monomials from its formal arithmetic output polynomial.

This includes the case with no degree-two monomials, which omits all 21. Constants, repeated wires, unary gates, and invalid references do not provide exceptions if their formal arithmetic semantics are defined as below. The proof still needs Lean implementation; the existing repository theorem supplies the lower-bound endpoint, not the pruning transformation.

## Formal semantics and the shadow

At an input wire use its variable. Interpret AND as multiplication and OR as addition, over polynomials with nonnegative integer coefficients. A nullary AND is 1, a nullary OR is 0, and a unary gate copies its operand. At gate evaluation time, an unavailable reference denotes polynomial 0, exactly matching the repository's false default. A repeated wire contributes twice to addition or twice as a factor to multiplication; in particular AND(x,x) produces x^2, not x.

These conventions were checked against `Defs/CircuitLowerBounds.lean`, lines 24–68, and `Defs/MetaComplexityLgpMono.lean`, lines 15–19. Nonzero coefficients can be ignored when comparing monomial support. On a Boolean assignment, the circuit is true exactly when some formal monomial has all its variables set to true.

Let P be the output polynomial and H the graph whose edges uv are precisely the squarefree monomials x_u*x_v occurring in P. Correctness of the circuit implies:

1. Every monomial of P has support containing a Heawood edge. Otherwise the assignment containing just its support would be a false positive.
2. Hence P has no constant, linear, or degree-two square monomials; H is a subgraph of Heawood.
3. If a Heawood edge uv is missing from H, evaluation on exactly {u,v} still requires a monomial with support {u,v}. It must have total degree at least three.

If H is nonempty, P therefore has minimum total degree two. Its minimum homogeneous component is exactly the edge polynomial of H, with arbitrary positive coefficients. If H is a proper nonempty subgraph, P is inhomogeneous.

## Size-preserving minimum-degree extraction

For a nonzero polynomial Q let d(Q) be its minimum total degree, and set d(0)=infinity. At each OR gate:

- If the two input minimum degrees differ, bypass the gate and use its lower-degree input.
- If they agree, keep the OR.

Keep AND gates and propagate the bypassed wire references. Nullary and unary gates may initially remain. Induction proves that every retained or bypassed wire computes the minimum-degree homogeneous component of its original polynomial. For an AND this is the product of the minimum components, including the zero case. For an OR it is the sum when degrees agree, otherwise the component from the lower-degree operand. No gate is added.

Strict saving: if P is inhomogeneous, at least one OR in its productive computation has operands of distinct finite minimum degrees. To see this, take the earliest inhomogeneous polynomial in that computation. Inputs and constants are homogeneous, products of homogeneous polynomials are homogeneous, and sums of homogeneous polynomials of the same degree are homogeneous. Thus this first inhomogeneous polynomial must be an OR of two nonzero homogeneous polynomials of different degrees. At least that OR is bypassed. A circuit of N gates consequently produces the shadow using at most N-1 gates.

The argument does not require fanout one. Every consumer can use the same bypassed wire, so no subcircuit is duplicated. Bypass all qualifying OR gates globally before deleting unused gates; even if a particular bypassed gate would later have become unused, it still contributes to the bound on retained gates.

When physically compacting the repository's gate list, remap references that were valid at the original gate's evaluation time. Keep every originally invalid reference as zero, for example by mapping it to a permanently out-of-range index. Blindly retaining or decrementing numerical wire indices is unsound because an originally invalid reference could otherwise acquire a value. This is an implementation obligation, not a mathematical counterexample.

## Applying the existing generic lower bound

The extracted circuit computes a homogeneous quadratic polynomial supported on H. Delete unused gates, propagate zero and positive constants, and remove unary copies. These operations add no gates. At this stage all productive nonconstant arithmetic gates have positive degree.

No productive multiplication can lie below another multiplication: that would yield a monomial of degree at least three at the output, and nonnegative arithmetic cannot remove it. Thus every remaining AND computes edge terms which survive through OR gates to the output. Its Boolean function implies the shadow graph function on all assignments, a stronger condition than the repository's pair-clean hypothesis.

`L_meta_1983.lean`, line 842, has the generic theorem `pairCleanBound` for every C4-free graph G, not just the full Heawood graph. It gives a vertex cover T with

`|E(G)| + |T| <= number_of_gates + 1`.

The shadow is a subgraph of Heawood, so it is still C4-free. The generic theorem therefore applies to the cleaned shadow circuit, including fanout sharing. There is no need to invoke the final, Heawood-specific single-level theorem for a graph with an edge removed.

## The needed vertex-cover calculation

The following three edge-disjoint perfect matchings partition the assignment's exact edge list:

```
M1 = [(0,7),(1,9),(2,8),(3,12),(4,13),(5,10),(6,11)]
M2 = [(0,8),(1,7),(2,13),(3,11),(4,10),(5,12),(6,9)]
M3 = [(0,10),(1,13),(2,12),(3,7),(4,11),(5,9),(6,8)]
```

A short exhaustive Python check found 24 perfect matchings and verified this partition. Each listed matching independently gives seven vertex-disjoint edges; no heavy search was used. Deleting one edge leaves two listed matchings intact. Deleting any two edges leaves at least one intact. Thus every such subgraph has vertex-cover number at least seven; the seven left vertices give the matching upper bound. This elementary certificate does not require invoking Konig's theorem.

If exactly one edge is missing from H, then |E(H)|=20 and every cover has at least seven vertices. The shadow needs at least 26 gates. But strict minimum-degree pruning of a circuit with at most 26 gates gives a shadow with at most 25 gates. Contradiction.

If no edge is missing, the same pruning without requiring strict saving yields a circuit of at most 26 gates for all 21 edges, whereas the generic bound requires 27. This also rules out that case directly, without using the external read-1 theorem.

Consequently at least two edges are missing. There is no inference here that two missing edges are sufficient for a witness.

## A further quantitative observation

Let r be the total number of binary OR gates with unequal minimum degrees in the original formal circuit, taking zero to have infinite degree. When the shadow is nonempty, bypassing all of them gives

`|E(H)| + tau(H) + r <= N + 1`.

For N=26 and exactly two missing edges, |E(H)|=19 and tau(H)=7, so r<=1. Inhomogeneity gives r>=1. Thus this case requires exactly one such OR and no additional gate loss during shadow cleanup. This stronger condition is mathematically plausible under the stated global bypass construction, but should receive independent review before use as an additional SAT pruning rule. The simpler at-least-two-missing-edges condition does not rely on counting all such gates.

## SAT implementation caution

For the team's ordinary constant-free binary networks, degree-one sets and degree-two edge sets suffice to test the main condition. An OR unions both sets; an AND has no degree-one terms, and its degree-two terms are cross-products of the degree-one sets of its operands. Degree-two monomials with repeated variables are squares and must not count as edges. Tracking only the 21 target edges is sufficient for the final missing-edge count, provided degree-one sets are exact. Require at least two missing target-edge bits at the output.

If the SAT encoding admits constant 1, unary gates, or invalid references, this recurrence needs corresponding degree-zero information and identity cases. The simplified recurrence cannot be reused unchanged in that larger model.

## Status

Mathematical review: PASS for at least two missing degree-two edges. The lower_bound agent independently examined the one-edge case and reported no hidden flaw, explicitly checking the first inhomogeneous OR, absence of squares, exact shadow support, and the 26-versus-25 contradiction. Existing generic lower-bound applicability: verified from the source statement. Finite matching certificate: checked by direct Python enumeration. Lean proof of extraction, strict gate saving, and constant cleanup: not implemented here. No claim that the posted existential statement is false follows.
