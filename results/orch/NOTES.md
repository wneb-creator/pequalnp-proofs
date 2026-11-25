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

### 2026-11-25T06:45:47.331233+00:00 library_route checked component

BadPairsBridge.lean compiled with exit 0 and empty log (566 lines). Full source /tmp/oec/pequalnp-pilot-73/library-route/BadPairsBridge.lean. Namespace PEqualNP.Outside.L_meta_2089.BadPairs. few_bad_posted takes the desk-style negative mask, maximality, and only the collinear rejection branch; it concludes one selected wire accepts at most 12 nonincident point-line pairs. The combinatorial cardinality proof is copied from checked L6208; new cross_bad uses pair-generated degenerate negatives. pair_maximal and rel_iff are finite kernel checks. Parent and reviewer notified.
Caution: a single hot wire accepting at most 12 bad pairs need NOT cost 62 gates. Example p OR edgeFunction(G−p) uses 60 gates and accepts 9 bad pairs. The simultaneous two-hot-wire condition remains essential.

- 2026-11-25T06:46:34.504725+00:00 counterexample: bounded 240-second stochastic search finished without witness. DONE 9437433 143 8. Best 63-gate final-AND candidate misses two of 52 positive edges and rejects all 236 promised negatives. This is only a heuristic search, not a lower-bound certificate.

- 2026-11-25T06:46:48.978208+00:00: structural_proof compiled full OR quota: for a hot wire false on any closed incidence cut, count(false input bits) ≤ |I|+1 for some set I of false OR gates no later than the wire. Frozen scratch structural/Quota.checked.lean; full log quota-build-6.log empty, exit 0. Uses root maximal_pair_cover plus counterexample Geometry definitions. This proves the quota component of checked reduction R_meta_2089_826 (modulo the definition bridge), but not the remaining 63-gate core.

- 2026-11-25T06:47:48.901617+00:00 restriction-route: Checked generic exact_on_two_points: any monotone function satisfying the owned promise agrees with the incidence edge function on every assignment with at most two active points. Finite geometry proves each 0/1/2-point set is itself a degenerate closed row. Dual two-line exactness is compiling. Existing checked smallgraph gate-elimination engine in L_meta_8487 gives +1/+2 per input restriction; by itself it is too weak for 64 gates on 26 variables and requires exact semantics. Naive degree+1 deletion needs unproved exclusivity of shared neighbor-sum gates.

### 2026-11-25T06:48:12.434142+00:00 library_route literature check

Primary source read 2026-11-25: Jukna, Disproving the Single Level Conjecture (SIAM J Comput 2006), author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf. Section 3.5 establishes graph-cover lower bounds specifically for single-level circuits; its cited K2,2-free edge-count bound is not an unrestricted-circuit theorem. The published normalization counterexamples use saturated bipartite extensions, so they do not directly refute a normal form for this pure bipartite promise. No general unrestricted 64-gate theorem was verified.

- 2026-11-25T06:48:18.944028+00:00 normal-form correction: P4 masking formula has5gates, but y AND (x OR z) OR z AND w has4gates. Thus only naive per-gate birth classification is disproved; cost-preserving minimal-circuit normalization remains possible. For flag negatives F_(p,l), the6 true variables intersect another flag row in0 or2 positions; each variable occurs in12of52 rows. One final factor rejects≥26 flagrows, each requiring19 falseORs, but sharing prevents simply adding quotas.

## 2026-11-25 06:48:20 UTC — independent quota/bridge/restriction review (status_review)

Source/math review PASS for partial preservation. Quota correctly forces a false input certificate to contain every zero of a closed maximal negative row, then bounds its size by false OR gates before the selected wire plus one. The bad-pair bridge equates Singer-library rows with the posted mask and uses only the collinear negative branch. Restriction proves exact behavior whenever at most two points or at most two lines are active; any accepted input with no incident edge must therefore have at least three points and three lines. Namespace/forbidden-token scan passed; options are permitted declaration-local limits; ordinary decide/decide +kernel only. Quota and bridge frozen compiled snapshots were provided; restriction was reviewed while its owner completed build4, awaiting frozen compile confirmation. Full target remains unproved.

- structural/Quota.checked.lean: 577 lines, SHA256 e05e45693c5e1aaa7184d8bc5bf35edb1bd67bec36b707117b90bf7be40c8b7f
- library-route/BadPairsBridge.lean: 566 lines, SHA256 10f2d6c18cf5dde7eff63a97b7ad3850d8d87b8abd940dd6b0210fc3a349e5ad
- restriction-route/Restriction.lean: 270 lines, SHA256 7a967168fce606177144c345aa49baa90a94c1a80041ccbb151dd8933aafd006

- 2026-11-25T06:50:19.717549+00:00 restriction-route: Frozen Restriction.checked.lean (270 lines; SHA256 7a967168fce606177144c345aa49baa90a94c1a80041ccbb151dd8933aafd006) compiled exit0, build-5.log empty. Adds exact_on_two_points, exact_on_two_lines, and spurious_input_large (accepted independent input needs at least3points and3lines). Independent status_review checked this exact SHA. Root notified immediately.

- Restriction research read 2026-11-25: Jukna On Graph Complexity, https://eccc.weizmann.ac.il/report/2004/005/ and primary PDF /revision/1/download/, gives formula/depth bounds (Theorem7.3), not the needed unrestricted circuit-size bound. Amano–Maruoka 2006, https://doi.org/10.1007/s00453-006-0073-0, states a gap between general quadratic monotone circuits and single-level circuits; no generic single-level normalization theorem was found.

## 2026-11-25 06:52:04 UTC — independent singleton review (status_review)

PASS for partial preservation: singletonInput/forcedBad/badPairSet and small_bad_singleton_support. Two distinct input singletons force at least 17 nonincident pairs by the checked finite incidence calculation; monotonicity maps their forced sets into badPairSet, so a function with at most 12 bad pairs accepts at most one singleton. Bool order proof and local DecidableRel instances are valid; only permitted declaration-local limits, no prohibited source text. Full target still unproved.

Singletons.lean SHA256 7a1ccdbfe2fbe3adc608128f2d5471072129e0363fa76527c3abe13a90a8dad6. Restriction.checked.lean was confirmed compiled with empty build-5.log and matches previously reviewed SHA256 7a967168fce606177144c345aa49baa90a94c1a80041ccbb151dd8933aafd006.
