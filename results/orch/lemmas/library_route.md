# Library strategy: L-meta-2592

## Sources

- Definitions root supplies definitions only; no direct circuit lower-bound theorem.
- Existing `lean/PEqualNP/Outside/L_meta_4725.lean` proves full Petersen requires at least fifteen non-NOT gates, with arbitrary NOT count. It adapts the branch-group argument from L_meta_2165 and L_meta_1549.
- R_meta_2592_271 already cuts our step into that bound and the case of one through four NOT gates.
- R_meta_2592_318 cuts at the last NOT; R_meta_2592_408 normalizes. All three reduction slots are occupied.

## Prepared partial

`/tmp/oec/pequalnp-pilot-99/library_route/Partial.lean` inlines L_meta_4725 and renames its helper namespace to PEqualNP.Outside.L_meta_2592. Added lemmas:

1. `binary_floor`: 15 + notCount C <= C.size.
2. `few_not_of_small`: a correct circuit of size <=19 has at most four NOT gates.
3. `many_not_impossible`: the target conclusion assuming at least five NOT gates.

Not yet compiled: root is provisioning Lean/cache. No sorry/new axiom. Only Mathlib.Tactic, Mathlib.Combinatorics.SimpleGraph.Basic, PEqualNP.Defs imports. Source helper local simp attributes are preserved. No claimed full proof.

## Remaining mathematical obstacle

The branch-count bound gives 15 binary gates and cannot by itself rule out 16-18 binary gates plus a few NOT gates. Other existing extensive certificates prove Petersen-minus-one vertex needs 14 binary gates. A gate-elimination argument may combine this with expensive input occurrences, but needs a rigorous structural lemma.

## Stronger partial discovered

L_meta_5236 has a signed truth-table certificate `atLeastSixteen`: even when x0 OR x2 is given free, the Petersen function requires at least sixteen binary gates. Its public theorem is only the seeded circuit case with three or four NOT gates, but the helper applies more generally.

Prepared `/tmp/oec/pequalnp-pilot-99/library_route/Partial16.lean`, inlining L_meta_5236 with namespace renamed, adding `Extended.realize_plain` seeded by the ten real input pins (a subset of the source initial list). This should yield `binary_floor16`, `few_not_of_small` (at most three NOT gates), and `many_not_impossible` for four or more NOT gates. Not yet compiled pending cache.

Found L_meta_6581 already provides the general sixteen-binary floor via the same signed certificate. Partial16.lean has now been rebased on that checked source rather than introducing new realization logic. Its remaining new content is arithmetic: sixteen plus NOT count is a gate lower bound, so size nineteen allows at most three NOT gates. This avoids new circuit semantic proofs.

## Strengthening search

- No `atLeastSeventeen`, `atLeastEighteen`, or `atLeastNineteen` certificate found in outside source files.
- Source L_meta_6581 has `nineFloor : Lower true inputs graph 15` for the nine-input vertex-deleted graph, and charges one additional binary gate when restoring the tenth essential input. Its generic contraction lemma is `projected_bound` (source line 583).
- L_meta_5236 gives the same sixteen-binary floor with one free nonedge OR x0 OR x2. Thus a first nonedge-OR gate can in principle be charged separately, giving a seventeen-binary floor for that first-gate case. Need an analogous certificate for the edge-OR orbit plus normalization to finish all first-gate cases.
- Direct strengthening to seventeen by gate elimination would need an extra eliminated binary gate beyond the source contraction's unit charge. The current floor is not enough to rule out one to three NOT gates at size nineteen.
