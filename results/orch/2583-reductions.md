# L-meta-2583: existing results and difficulty audit

Updated 2026-11-25T14:48:08.425528+00:00

The held statement says every exact-two-input, backwards-only AND/OR circuit for a finite projective-plane incidence function has a no-larger circuit with a read-1 proof tree for every prime implicant. `IsReadK ... 1` is existential per implicant and jointly bounds both endpoint multiplicities; it is not fanout-one or syntactic read-once. The plane hypotheses give N=q²+q+1, each line q+1 points, and exactly one common line for two distinct points. No missing arity or invalid-forward-wire escape appears: `TopForm.IsAO2` rules those out.

## Useful checked results

- `L_meta_7684.lean` (1126 lines): any finite bipartite edge set E and vertex cover A,B have a read-1 AO2 realization with size ≤ |E|+|A|+|B|−1. Root assigned lean_structure to adapt this.
- `L_meta_4897.lean` (1961 lines): for a C4-free bipartite graph, a correct read-1 AO2 circuit implies a vertex cover A,B with |E|+|A|+|B|≤size+1.
- `L_meta_7639.lean` (1977 lines): if that C4-free graph has a perfect matching, correct read-1 circuits satisfy |E|+N≤size+1.
- `L_meta_2237.lean` (1878 lines) and `L_meta_6369.lean` (1397 lines): general SimpleGraph versions, no C4 and read1 imply |E|+vertex-cover-size≤size+1.
- `L_meta_6579.lean` (378 lines): a syntactically separated circuit whose AND inputs are pure point-OR and line-OR wires is read1.

## Exact equivalence driving difficulty

For a plane, regularity gives |E|=N(q+1), and a perfect matching gives minimum vertex-cover size N. Hence the desired normalization implies the sharp unrestricted lower bound N(q+2)≤C.size+1. Conversely that sharp bound plus the all-points star construction proves normalization. Thus the hard issue is the exact AO2 circuit lower bound, not the construction or ReadK bookkeeping.

## Open related steps

Live public feed https://data.pequalnp.com/data/desk/gaps.json, updated 2026-11-25T14:44:25.860Z:

- L-meta-4895: general C4-free bipartite read1 normalization, open; three live cuts. Its first cut uses unrestricted vertex-cover budget L-meta-2872 plus the now-checked construction7684.
- L-meta-2872: unrestricted cover-budget lower bound, open; three cuts.
- L-meta-2976: no-larger two-level separated normalization, open; three cuts.
- L-meta-972: plane order3 (26 vertices,52 edges), unrestricted AND/OR lower bound64, open. This is already a necessary special case of our all-q statement.
- L-meta-2583: held statement itself, open, zero reductions; lease terms explicitly reductions_open=false. No reduction may be submitted.

## Small-plane checked bounds

IMPORTANT: L-meta-971 is checked, and proves the full unrestricted Monotone2 lower bound27 for the14-input Heawood/Fano incidence function. Its source has only Defs import. Consequently a26-gate AO2 Fano counterexample cannot exist; exact_synthesis was notified.

`L_meta_971.lean` is9367 lines/472258 bytes. Its final theorem normalizes the circuit, classifies14 canonical configurations of ineligible inputs, then excludes each. It is highly Fano-specific rather than a generic-q argument; direct inlining plus7684 would threaten512KiB file cap without substantial trimming. A possible q2 partial would also need finite-plane isomorphism/relabeling.

`L_meta_1983.lean` is a shorter1348-line Fano lower27 proof, but requires no AND gate in any AND cone. `L_meta_4803.lean` similarly gives order3 lower64 under no nested AND. Other checked order3 lower64 results require line-degree1, TopForm/junk-empty, or similar substantive conditions. They do not give the unrestricted theorem.

`L_meta_5733.lean` normalizes AND gates below the target only for acyclic graphs or cycles, so it cannot be applied to a plane incidence graph.

## Current assessment

A complete proof would settle the still-open order3 exact lower bound and its all-order generalization. The desk itself explicitly identifies the missing mathematics: mixed blocks that accept edges without a single star must be charged at least the star-cover cost even when they share gates. Existing machinery settles syntactic pure-star blocks and read1 circuits, but not this charging step. Small finite checks can certify Fano/order3 subcases but cannot establish the all-q statement.

Records: `/tmp/oec/pequalnp-pilot-98/2583-public-gaps.json`, `2583-read1-statements.json`, `2583-bound-statements.json`, and `2583-order3-statements.json` contain full saved census data.

## Verified local adaptations (2026-11-25 14:51 UTC)

`results/orch/lemmas/2583_lower.lean` compiles using only `PEqualNP.Defs`; `PEqualNP.Outside.L_meta_2583.ReadOneLower.matching_bound` is the adapted L_meta_7639 theorem under target-owned namespaces. Full check output is preserved in `results/orch/2583-lower-check.log` (exit 0, inherited warnings only).

`results/orch/lemmas/2583_hall.lean` gives point degree at most q+1, the Hall condition, and an incidence perfect matching `PlaneMatching.plane_perfect_matching`. Its first standalone compile passed without warnings; a Defs-only recheck is now running. The direct imports are being reduced to exactly the final allowed imports before assembly.

2026-11-25 14:54 UTC: The Hall proof now compiles with only `PEqualNP.Defs`, after copying the finite Hall induction from pinned Mathlib into `PlaneMatching.FiniteHall`. This adds about 200 lines and is independently audited as semantically identical. The combined candidate proves the sharp read1 gate bound and the exact equivalence between the held conclusion and the unrestricted gate budget; these are explicitly partial progress, not a proof of the unrestricted budget.

Hall validation chronology: `2583-hall-check.log` is the initial extra-import compile (exit 0); `2583-hall-defs-check.log` is the initial Defs-only attempt (exit 1, missing Hall theorem); `2583-hall-inline-check.log` is the Defs-only compile with local finite Hall induction (exit 0). The final combined check also includes the comment-format cleanup required by independent review.
