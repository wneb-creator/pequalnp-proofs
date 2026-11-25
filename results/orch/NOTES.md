# Pilot 73 orchestration notes

Task: L-meta-2089, leased 2026-11-25 06:35:43 UTC.
Exact desk statement is saved in /tmp/oec/pequalnp-pilot-73/desk-2.json.
Only root contacts the desk, renews, commits, pushes, and submits.
No Lean source changes outside the named proof file without coordinating with root; use task scratch for proof experiments.
Lean environment: ELAN_HOME=/tmp/oec/pequalnp-pilot-73/elan, prepend its bin directory to PATH.
Pinned Lean 4.36.0 and Mathlib cache ready; never lake update or build Mathlib from source.

## Current facts

- Posted target is an AND-output lower bound for order-3 projective-plane incidence.
- Prior circuit has at most 62 gates, two distinct selected wires, and their AND must match all incident pairs and all degenerate maximal false inputs.
- Goal is False.
- Only project import allowed: PEqualNP.Defs.
- Reductions enabled; three live reductions already reported.
- No open proof PRs reported by the desk.

## Strategy updates

Each agent should append a short timestamped result here using a separate append operation; avoid rewriting others' notes.


- 2026-11-25T06:37:58.921259+00:00 counterexample: enumerated all 8192 point subsets. There are 704 maximal false rectangles, 236 degenerate promised ones. All 117 nonincident pairs occur in promised negatives; all-point and all-line assignments are promised negatives. Hence every separator has the exact 52-edge degree-two shadow and no same-side/singleton minterms. Larger minterms remain unconstrained in 468 nondegenerate maximal rectangles. Data: scratch counterexample/promises.json.

## 2026-11-25 06:39:18 UTC — reduction review (status_review)

All three existing reductions of L-meta-2089 are open in the public desk snapshot (updated 2026-11-25T06:32:12.838Z). Join caps reductions at three per step; reductions_live=3 means a fourth is outside the stated allowance. No submission attempted.

| Reduction | Children / current status | Meaning |
|---|---|---|
| R_meta_2089_1 | L-meta-4239 CHECKED; L-meta-4241 open | Finite geometry classification; 63-gate AND-pair lower-bound core |
| R_meta_2089_2 | L-meta-4787 open; L-meta-4789 open | Single cold OR test on ≤60 gates; minimal family of at least two cold OR tests with C.size+2*K.card≤64 |
| R_meta_2089_826 | L-meta-5863 CHECKED; L-meta-5865 open; L-meta-5867 open | Gate replacement; false-OR quota; minimal circuit obstruction |
| R_meta_1684_1 | L-meta-2416 CHECKED; L-meta-2418 open; L-meta-2420 open | Correctness on one-line inputs; degree-one extraction; degree-one counting |
| R_meta_1684_2 | L-meta-2089 open; L-meta-2091 open | Final AND gate / final OR gate cases |
| R_meta_1684_3 | L-meta-2716 open; L-meta-2718 open | Degree-one lower bound; normal form up to point-line duality |

Checked files L_meta_4239.lean, L_meta_5863.lean, L_meta_2416.lean are present locally and can be copied into the target namespace when needed (only Defs+Mathlib are permitted project inputs). There is no fully solved reduction to apply directly. L2418 has public open PRs 8144/10913; L2420 PR4507; L2716 PR4938.

R2089_826's quota is conceptually an OR-gate sensitivity bound: a hot wire false at maximal false x must switch true when any zero input is enabled; its false OR dependency graph therefore needs at least count(false x)-1 OR gates. Even after proving this, the core L5867 retains the hard 63-gate lower bound. R2089_1's geometry proof L4239 is 144 lines and straightforward to inline if root chooses its direct core route.

Deeper cuts inspected: R4241_369 transfers from degenerate maximal rows to all nonincident degenerate rectangles; its geometry child L6824 remains open. R4241_644 abstracts circuits to trimmed families of false certificates but still assumes a 63-step cover-cost lower bound. R4787_1 normalizes fan-in/backward references; R4787_2 reduces negative tests to 20 cyclic-orbit representatives. R4789_407/418/521 give resource-count cuts but retain substantial obstruction hypotheses. None supplies a completed lower bound.

Correction: measured line counts are L4239=122, L5863=154, L2416=160 (the earlier 144 estimate for L4239 was incorrect).

## 2026-11-25 06:40:07 UTC — independent partial-preservation review (status_review)

Reviewed root maximal_pair_cover, structural weighted_cut, and geometry delta/incidence/separated_points/singleton_maximal/incidence_refl source. PASS for mathematical validity and namespace/forbidden-source rules; all helpers are isolated under PEqualNP.Outside.L_meta_2089, ordinary proof terms/tactics, no new axioms/sorry/native evaluation. Weighted descending-frontier induction charges each possible branching O gate once. Geometry uses ordinary decide on a finite proposition. The exact target theorem remains intentionally absent, so this is approval to preserve partial work only, not a full proof/checker/PR verdict. Structural build log predates cosmetic edits; rebuild the merged current source before asserting it compiles.

### 2026-11-25T06:41:34.278006+00:00 library_route

- Existing checked geometry L_meta_4239 and replacement L_meta_5863 can be copied into allowed module namespace. No direct circuit lower bounds available through Defs.
- Exhaustive Python geometry census: 704 maximal false rows; 236 degenerate rows, types (0,13):1,(1,9):13,(2,6):78,(3,3):52,(6,2):78,(9,1):13,(13,0):1. Remaining 468 generic rows are (3,4) or (4,3).
- Any independent input with at most 2 points or at most 2 lines extends to a degenerate row. Thus spurious minterms of a promised circuit need at least 3 points AND 3 lines.
- Building a new adaptation of L_meta_6206 plus copied L_meta_6208: AND rejection of only pair-generated degenerate rows already implies one operand accepts at most 12 nonincident point-line pairs. Scratch BadPairs.lean and complete build log under /tmp/oec/pequalnp-pilot-73/library-route/.

- 2026-11-25T06:41:52.346584+00:00 counterexample: Geometry.lean extended and Lean-checked (exit 0, empty log). Abstract monotone function satisfying promise rejects all nonincident pairs and all one-sided inputs; pair_truth_iff recovers exact incidence shadow. Scratch file /tmp/oec/pequalnp-pilot-73/counterexample/Geometry.lean, now 138 lines. Beginning bounded stochastic local optimization from a known 65-gate final-AND separator to test 63-gate candidates.

- 2026-11-25T06:42:19.696277+00:00: structural_proof compiled generic false_certificate in scratch structural/Structural.checked.lean. Every false wire has a raw-input false certificate B with |B| ≤ number of false OR gates in its prefix + 1. Handles forward/out-of-bounds references. Full build log structural-build-3.log is empty (exit 0). Geometry should force B to contain all zeros at closed independent-set inputs.

- 2026-11-25T06:43:29.217421+00:00 normal-form: compiled scratch normal-form/NormalForm.lean: nf_common_lines (kernel-checked unique common line), nf_rectangle (all-incident rectangle has a singleton side). Full lake env lean exit 0, build.log empty. A naive AND-birth biclique cover is invalid: P4 edge function xy OR yz OR zw = (x OR z) AND (y OR w) AND (y OR z); first AND creates bad xw, final AND deletes it, total 5 gates. Need global counting invariant.

## 2026-11-25 06:43:29 UTC — independent second partial review (status_review)

PASS for partial preservation, not full target completion. Reviewed structural false_certificate, geometry pair-truth/one-side rejection, and BadPairs.cross_bad/few_bad with copied combinatorial count proof. Gate semantics explicitly handle forward/missing references as false. Geometry keeps monotonicity/negative-row hypotheses explicit. Bad-pair cross incidence follows from pair-generated degenerate cuts, then ≤12 follows from finite projective-plane counting. Namespace isolation and forbidden-source scans passed; ordinary decide and decide +kernel are used, no new axioms or placeholders. Root must rebuild merged source.

- Structural.checked.lean: 294 lines, SHA256 c6c2690e88c64ae3bea58478f941bfa9f60950f7aec9de6f9c3a774bfbc2bd2c
- Geometry.lean: 131 lines, SHA256 b16dfed8f3ed6b286bb6aa018621cc977f8d9a1df5a0ab2823ff89c1eff34b38
- BadPairs.lean: 489 lines, SHA256 746e585969dd470927d0540769160a2d7ff8287a4cacc2bf0417192779d5b1f4

- 2026-11-25T06:44:26.098777+00:00 counterexample correction: final Geometry.lean line count is 131 (prior 138 was an estimate). Kernel check exit 0. Stochastic run still has only a near-witness: 63 gates, final AND, two missing positive edges, zero false positives. This is not a counterexample.
