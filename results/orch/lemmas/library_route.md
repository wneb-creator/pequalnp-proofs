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

## Verified SAT/LRAT route (14:02 UTC)

Read Defs/LratEncoding.lean. `enc` and `enc2` encode AND/OR/TRUE-padding circuits, not NOT gates. The definitions include invalid-source-as-false, arbitrary output selection, normalization, and adjacent independent-gate ordering.

- L_meta_5050.lean has generic normalization/completeness and cube covering for arbitrary n,s, despite its public theorem specializing n=14,s=26; `main` is used at final line 1465. Around 1460 lines total.
- L_meta_3644.lean has the basic monotone `valid_ofCirc`, `exists_nf`, and `enc_sat` bridge, around 1040 lines.
- L_meta_5531.lean contains a proved generic LRAT checker: `check_sound` line 540, `checkW_sound` line 546 (compressed words), `checkFirst_sound` line 552. Generic checker can replay any suitable CNF certificate.
- No verified NOT-capable synthesis encoding was found among 48 Outside files selected by SAT/CNF/LRAT terminology. Signed truth-table search certificates are a separate route and do permit complements for free.

A direct completeness proof for unnormalized NOT circuits could avoid the expensive structural part: four operation slots AND/OR/NOT/TRUE, false extra source at each step, arbitrary output, pad with OR(false,false), encode invalid/future reads as false, duplicate unary AND/OR sources. Existing solver symmetry constraints would need their own normalization proofs before a certificate covers all possible circuits.

Further finite-search lead: L_meta_4807.lean defines `Live target k t S` with both total gate count k and NOT count t (lines 18-24), explicit unary NOT and binary AND/OR transitions, and a verified cover/checker framework. This is not CNF, but it is a ready semantic model for counting negations, unlike the free-complement certificate in Partial16. Existing instance uses BitVec512 / nine inputs and seeded monotone final theorem; no full ten-input nineteen-gate instance found.

## Compilation result

2026-11-25T14:09:50.240117+00:00: Partial16.lean compiled with exit 0 using pinned Lean v4.36.0 via lake env lean. Full logs: /tmp/oec/pequalnp-pilot-99/library_route/partial16.stdout and .stderr. 172 inherited linter warnings, zero errors. This is a checked partial bound, not the full posted theorem. Parent notified immediately for push.

## 2026-11-25 14:22 UTC: seventeen-binary strengthening

The independently compiled retention wrapper shows both inputs of the first signed binary gate remain in its tail pool. Arbitrary Petersen-vertex deletion projections are now being Lean checked in `Projection17.lean`; each maps the full target to the existing nine-vertex graph with signed lower bound fifteen. A lightweight `ProjectionHarness.lean` contains the original contraction model and uses `nineFloor` only as an explicit hypothesis, not an axiom. Its `tail_bound_left` charges the retained deleted pin as a constant, giving at least sixteen tail gates and seventeen binary gates in total.

Prepared `Seventeen.lean.txt` combines retention and projection and derives at most two NOT gates for a computing circuit of size at most nineteen. The lower_bound agent separately prepares a two-constant charge for first AND-type gates, giving eighteen binary gates in that case. Generic duplicate-root charging for first OR is invalid (a multiplexer counterexample); reduction_strategy investigates the Petersen-specific next-gate structure.

The initial Partial16 cache export failed because Lean required an explicit package root for an output olean. Corrected command uses `lean -R /tmp/oec/pequalnp-pilot-99/library_route -o .../Partial16.olean`; one corrected base cache build is running.
