# L-meta-1735: preserved partial results, no accepted submission

The exact posted statement remains unproved. No refutation was found. No proof PR was opened, because the local checker rejects the helper-only named file with `REJECTED (no-theorem)`. This research branch is an archive, not a single-file submission branch.

## Checked Lean components

- `lean/PEqualNP/Outside/L_meta_1735.lean`: 3217 lines, SHA256 `c4727b0197e1cec0f82aa36b9643e3cd225333f070889fa540af0fadc09b2328`. The canonical file combines a uniform bound for at most two junk gates with a bound for arbitrary fixed AND depth. The depth constant depends on the chosen depth cap. The unrestricted universal constant is not proved.
- `lemmas/nested_two.lean`: explicit constant 4 for exactly two nested junk AND gates, using a four-center neighborhood cover and graph support counting.
- `lemmas/at_most_two.lean`: combines the nested result with the existing parallel-junk bound.
- `lemmas/fixed_depth.lean`: a rank certificate bounded by D yields `edgeFinset.card <= size * gateBound D`, without leastness or TopForm. Its Ustar corollary remains dependent on D.
- `lemmas/contextual_essential.lean`: necessary positive-edge witnesses for OR bypasses in a least circuit. This is a separate checked partial and does not provide a bounded-load charging argument.

All newly composed final helper conclusions were axiom-audited using only `propext`, `Classical.choice`, and `Quot.sound`, and independently reviewed before pushing.

## Build and checker

`lake build PEqualNP.Outside.L_meta_1735` passed: exit 0, 16.60 seconds, peak 3,787,372 KiB. The complete build log and metrics are preserved.

The actual local checker ran on the unchanged 3217-line canonical file: exit 1, 77.44 seconds, peak 13,725,160 KiB. Exact verdict:

`REJECTED (no-theorem): the file declares no theorem named PEqualNP.Outside.L_meta_1735 (one lemma, one file: the theorem carries the module's name)`

A successful partial build is not acceptance of the posted theorem. The capped post-acceptance cleanup pass was not applicable. Canonical lines before/after that omitted pass: 3217 / 3217.

## Remaining mathematical obstacle

The unresolved case has arbitrarily many nested junk AND gates. Pair-only evaluations omit essential independent-set semantics. Applying the two-junk neighborhood argument separately at many frontiers repeats the entire graph-support charge and supplies no uniform total. Fixed-depth witness budgets grow with D.

Concrete nonleast examples show that TopForm, fanin incomparability, essential child bypasses, and even irreducibility under every single-gate replacement by an earlier wire do not eliminate nested junk. The twelve-gate C5 example resists all 126 such replacements but has an explicit seven-gate comparator. These examples refute proposed shortcuts, not the posted statement.

Finite SAT exclusions are ordinary computational results, not Lean certificates. The two final capped searches both returned UNKNOWN after 300 seconds; neither produced a proof or a counterexample. All controls are labeled nonleast. The desk reported reductions_live=3 at assignment. The later public review found three merged reductions and a subsequent reduce-extra rejection, with no evidence of a free slot, so no additional reduction was submitted.

## Desk and prior work

Two desk assignments were received; null-answer count: 0. No other pilot's lease was used or released. The initial L-meta-2602 lease became invalid with HTTP 410 despite an earlier future expiry; all then-current results were pushed before requesting another assignment. The exact response body was `{"error":"no such live lease: it expired or was released. Ask /desk/next again."}`. Complete headers/body are preserved in `results/orch/desk/auto-beat-011-diagnostic.txt`.

The desk then assigned L-meta-1735. Lease renewal evidence is being preserved separately; final release disposition will be recorded before closing this job. No exact proof or refutation of L-meta-2602 was obtained either; its checked partials, finite searches, and checker rejection are preserved under `results/orch/` and its named Lean file.

KIT-MESSAGE-ID msg-07569722ae629e1f3149d063
Sub-agents: finite_search, independent_review, lemma_route, status_review, structure_proof, toolchain
