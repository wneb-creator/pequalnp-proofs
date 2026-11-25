# L-meta-1031 research handoff

The posted theorem remains unproved. No refutation of that theorem was found, and no proof PR was opened. This branch preserves partial Lean results and search evidence; it is not a single-file submission branch.

The named file is `lean/PEqualNP/Outside/L_meta_1031.lean`. Its 6,066 lines have SHA256 `2011a533d49ecf0a82d095ef56836673c07337a6174bdb870e66edab55aad8e3`. The named build completed successfully with 5,183 jobs. Complete output is in `named-v2-build.stdout` and `named-v2-build.stderr`.

The local posted-statement checker did not return a verdict. The latest attempt exited 3 with `CHECKER FAULT: the verifier ended without a verdict (exit 137).` Its complete output is in `named-v2-checker.stdout` and `named-v2-checker.stderr`. No checker acceptance or rejection is claimed. The exact final theorem is absent from the partial file.

## Reusable Lean results

- `graph_has_minimum` proves existence of a size-minimum monotone binary circuit for any finite graph.
- `graph_has_stars` constructs a circuit with the requested nonempty star ownership, without minimum size.
- `ForestCase.forest_optimal` proves the exact existential conclusion of the posted statement under the additional hypothesis `G.IsAcyclic`.
- Empty graphs and graphs whose edges have a common center are also covered.
- `finish_from_pair_normalization` derives the full posted theorem from an explicit, unproved hypothesis giving a minimum circuit whose AND gates accept only adjacent vertex pairs. It does not discharge that hypothesis.
- Additional lemmas establish relevant gates, edge witnesses, strict binary circuit structure, last-AND soundness, and a sufficient earlier-wire replacement criterion for contradicting minimum size.
- `CounterOr.violates_or_edge_bound` gives a Lean-checked counterexample to the auxiliary claim that every circuit needs at least `|E|-1` OR gates. The graph has eight vertices and ten edges, no triangles or four-cycles, and the exhibited circuit has eight OR and six AND gates. Its total size is fourteen, while this graph has a thirteen-gate circuit. This is not a refutation of the posted theorem.

## What is missing

The two existence results use different witnesses. A full proof must show that a size-minimum circuit can be chosen with the ownership property. None of the present lemmas proves a transformation that repairs interacting AND gates while preserving minimum size.

In particular, a gate may be essential on positive edge inputs while owning no edge. Replacing an earlier dirty conjunction by one input can lose needed edges; replacing it by a disjunction can introduce nonedges. Shared OR subcircuits also prevent simply cleaning each conjunction independently and adding the costs.

The reduction route was unavailable: the desk reported all three reduction slots live for this step. No fourth reduction or conditional proof submission was made.

## Search evidence and its limits

The frozen `search`, `search-round2`, `search-round3`, and `search-round4` directories contain full logs, sources, witnesses, and SHA256 manifests. Each README states its model restrictions. Further final searches, if present, are recorded separately in `search-round5`.

External SAT/SMT results are computational evidence, not Lean lower-bound proofs. An exact-size UNSAT result for a model requiring live, distinct gates does not alone exclude every smaller size. A timeout is unknown. Cone-cost models may overcount shared proper sub-conjunctions and therefore cannot establish unrestricted impossibility from UNSAT alone.

A circuit below the canonical `|E| + minimumVertexCover - 1` cost would also not, by itself, refute the posted ownership theorem: an appropriate lower bound for every circuit with that ownership property would still be needed.

## Continuation

Read `NOTES.md` and the final obstruction reports before retrying local deletion or separate AND/OR counting. The strongest unresolved routes are a global size-preserving normalization of interacting conjunctions, or a finite counterexample together with a checked lower bound excluding every circuit satisfying the ownership property.

The current source and all completed proof checkpoints were pushed to `origin/pnp/pilot-56`. Keep branch artifacts separate from any eventual PR: a proof PR must have a net diff adding only the named Lean file and must contain the exact final theorem.
