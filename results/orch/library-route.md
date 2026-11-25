# Library route: L-meta-2583

Current upstream contains no checked exact normalization proof found. The stronger C4-free bipartite normalization claim remains represented by reductions R_meta_4895_1, R_meta_4895_215, R_meta_4895_628. Their main unresolved premise is the sharp matching charge |E|+|M| ≤ size(C)+1.

Useful existing proof bodies (must inline because assigned imports allow only PEqualNP.Defs):

- L_meta_7684.lean, 1126 lines: constructive AO2/read1 circuit for bipartite E with vertex cover A,B, size ≤ |E|+|A|+|B|-1. Combines L_meta_3692 star builder and L_meta_6579 read1 invariant.
- L_meta_4897.lean: converse lower bound for circuits already read1, with extracted cover.
- L_meta_7639.lean: read1 matching charge |E|+n ≤ size(C)+1 when E has perfect matching.
- L_meta_7344.lean: general quadratic-prime-implicant normalization at factor 3 with surcharge for unread prime implicants, too weak for exact size.
- L_meta_2581.lean: constant-factor incidence lower bound for read3 circuits, also insufficient.

Plan: specialize copied L_meta_7684 builder to the plane, using all points as cover. Obtain read1 circuit of size at most N*(q+2)-1. Exact original theorem would follow from sharp lower bound N*(q+2) ≤ C.size+1 for arbitrary AO2 incidence circuits. This is the central unresolved mathematical issue, not a Lean missing-lemma issue.

Prepared `results/orch/lemmas/library_lower.lean`: inlined 2988 in namespace `PEqualNP.Outside.L_meta_2583_aux.LibraryLower`, plus `lower_threeN` with exact posted assumptions and conclusion `3*N ≤ C.size+1`. Not yet Lean-checked because root is restoring toolchain/cache.

Semantic gate-count route: conjecturally split sharp bound into OR-count ≥ |E|−1 and AND-count ≥ vertex-cover number for bipartite C4-free graph functions. Both remain unproved. Exhaustive 5-variable enumeration with arbitrary free ORs found no exact C4-free graph output with two AND gates and cover number greater than two (285 first-AND functions; 1.48 seconds). L_meta_1006 refutes boundary-only AND-count claim on a nonbipartite C4-free graph, but its circuit disagrees with the graph function on 39/2048 inputs, so it is not a full-correctness counterexample.

A dual exhaustive search with at most two OR gates and arbitrary free ANDs found no 5-variable C4-free graph function with at least four edges (285 first-OR functions, 372 target graphs, 0.97 seconds). The conjectured OR-count bound is equivalent by De Morgan duality to an AND-count lower bound for monotone 2-CNF. Four-cycles permit the familiar factorization of four clauses, but ruling out more subtle Boolean absorption in arbitrary DAG circuits is unresolved.

Stopped on root instruction after lease reported no longer live. No exact OR-count proof found. Constructive result delivered: lower_threeN under exact posted hypotheses; standalone Lean check exit0. The parent also compiled it in the named module. The sharp bound gap remains from 3N−1 to N(q+2)−1.
