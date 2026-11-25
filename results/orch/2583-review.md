# Independent statement audit: L-meta-2583

Audit UTC: 2026-11-25T14:48:47.648325+00:00
Exact assignment read from `/tmp/oec/pequalnp-pilot-98/desk-rerequest.json`.

No counterexample or definitional loophole found. This is a substantive size-preserving normalization problem, not an automatic consequence of monotonicity.

`IsAO2` means AND/OR only, exactly two inputs per gate, with every gate reading earlier wires. Repetitions and unused gates are allowed; output need not be last. Although the model does not explicitly bound the output index, computing this nonconstant incidence function excludes a missing output. Singleton inputs all produce false, so the output cannot be an input wire either. Constants, empty gates and forward reads cannot supply a shortcut under the assumptions.

`IsReadK ... 1` is joint existential proof-tree multiplicity for each prime implicant. It is not global syntactic read-once, and it is not separate per-variable minimization. The incidence function's prime implicants are precisely one incident point/line pair, with distinct coordinates because the two Fin embeddings occupy disjoint halves. There is no vacuity caused by missing prime implicants. A correct circuit itself need not be read-1: adding a redundant AND with an expression already implied by a pair can force repeated leaves; the target asks for a replacement circuit.

The incidence axioms do not obviously admit degenerate planes. q≥2 implies N≥7 and each line has at least three points. A pair of distinct lines cannot contain two common points, by uniqueness of the line through those points. For any point, the other N−1=q(q+1) points partition into q-element sets on its incident lines, forcing degree q+1. This counting argument is mathematical audit, not a Lean-checked lemma here. In particular, empty/duplicate lines and isolated points do not create an immediate refutation.

Relevant existing local results:

- `L_meta_7684` constructs a read-1 AO2 circuit from any bipartite vertex cover with size at most |E|+|cover|−1. The new partial incorporates it in the allowed file.
- `L_meta_2237` gives a vertex cover T with |E|+|T|≤C.size+1 for a read-1 AO2 circuit of a C4-free graph. For a projective-plane incidence graph, regularity and a perfect matching make the least cover size N. Thus size-preserving normalization would imply the sharp N(q+2)−1 lower bound, matching the point-star construction. The matching/counting implications are not formalized by this audit.
- `L_meta_2581` assumes read-3 and gives a constant-factor bound; `L_meta_1942` assumes read-2 and gives factor100. Neither supplies size-preserving normalization.
- `R_meta_2976_418` takes the more general C4-free bipartite normalization as a hypothesis. A hypothesis in a reduction is not an already-proved normalization theorem.

Public status was read from the public export generated 2026-11-25T14:44:25.860Z. Both node2583 and node2592 have conjecture status code j, rather than checked/refuted. Snapshot paths are `/tmp/oec/pequalnp-pilot-98/head-2583-review.json`, `2583-public-map.json`, and `2583-public-meta.json`. Public source: https://data.pequalnp.com/data/map/program/meta_complexity.2695b786f67a.json . This does not explain the old lease's HTTP410. The exact reason for that lease failure is UNVERIFIED from this public data; no lease was queried or mutated by this audit.
