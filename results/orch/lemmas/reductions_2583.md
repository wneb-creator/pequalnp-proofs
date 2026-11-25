# L-meta-2583 corpus and construction

The lease closes reductions; no cut may be submitted. No existing reduction of L-meta-2583 appears in the public feed snapshot.

## Read-1 interpretation

Read-1 means every prime implicant has some proof tree in which each variable occurs at most once. It is not a requirement that each input be read once throughout the circuit. The incidence function has prime implicants exactly its point-line edges.

## Relevant checked sources

- L_meta_7684, 1126 lines: for any bipartite edge set E and vertex cover T, constructs a read-1 AO2 circuit of size at most |E| + |T| - 1.
- L_meta_4897, 1961 lines: a read-1 AO2 circuit for a C4-free bipartite graph yields a vertex cover with |E| + |T| <= size + 1.
- L_meta_7639, 1977 lines: with a perfect matching, the read-1 lower bound is |E| + N <= size + 1.
- L_meta_2581, 1048 lines: read-3 plane circuits obey a constant-factor lower bound, not read-1 replacement.
- L_meta_1942 and L_meta_2058: read-2 plane lower bounds, not no-larger replacement.

## Constructed partial

`reductions_2583_upper.lean` is self-contained with imports Mathlib.Tactic and PEqualNP.Defs, in namespace PEqualNP.Outside.L_meta_2583_aux. It transplants L_meta_7684 and supplies:

- incidenceEdges_card: line degree q+1 gives |E| = N(q+1).
- incidence_read1_upper: a read-1 AO2 circuit for the exact incidence expression exists with size <= N(q+2)-1.
- large_circuit_case: therefore the requested no-larger read-1 replacement exists whenever C.size >= N(q+2)-1.

The edge-count proof is adapted from the checked allEdges_card helper of L_meta_2581. These helpers use only the uniform line-size assumption; q>=2 and pair-uniqueness are unnecessary for the upper bound.

Local Lean compilation passed with exit 0 on 2026-11-25T14:46:58.410080+00:00. The unresolved full theorem is the small-circuit case C.size < N(q+2)-1. Given regularity, perfect matching and the read-1 lower bound, this is essentially the exact unrestricted monotone incidence-circuit lower bound.
