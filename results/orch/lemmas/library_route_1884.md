# L-meta-1884 library route

No full proof or refutation is claimed.

## Existing reductions and exact dependencies

- `R_meta_1884_773.lean` reduces to relabeling, arbitrary-unary normalization, and the canonical free-complement lower bound. Its first two children are exactly checked `L_meta_2594.lean` (same-size relabeling) and `L_meta_2596.lean` (replace an arbitrary unary extra input by the complement, no size increase, except direct extra-input output). Public child `L-meta-2598` is still conjecture: no18-gate circuit on x plus !x0 computes Petersen. This is the core, not a solved theorem.
- `R_meta_1884_1.lean` has four hypotheses: ordinary Petersen no≤18, Petersen-minus-vertex no≤15, and two exceptional low-reader patterns involving input0 and its free complement10. The P9 hypothesis is fully solved by the internal `graphLower` theorem at L8367 line6860, despite its exported final theorem having additional Strict/notCount assumptions. No unconditional ordinary Petersen≥19 theorem was found in the final-header census. Reduction_strategy investigates the reader-pattern cases.
- `R_meta_1884_412.lean` uses finite two-pin pivotality and a semantic circuit core. Its PR8799 explicitly leaves that core open. Monotonicity, graph automorphism invariance, and three probes characterize correctness; they do not remove the lower-bound obstruction. The PR also gives NOT circuits passing all30 global boundary rows or all38 cofactor boundary rows but failing full truth-table correctness. Counterexample agent was warned and already checks all1024 rows.

Other useful checked statements: L5367 gives15 plus the number of gates actively reading0 or10 at most circuit size. L7314 turns a canonical free-complement circuit≤18 into an ordinary18-gate circuit except possibly size18/output28/noNOTreading10. L9818 excludes≤16 gates for Petersen with edges01 and12 deleted; it is not a full Petersen19 bound. L4934 supplies bounded same-size relabeling (indices≤29).

## P9 extraction

`/tmp/oec/pequalnp-pilot-99/gap1884/library_route/Pv16.lean` is exactly checked L8367 through its `graphLower`, with namespace renamed to `PEqualNP.Outside.L_meta_1884.Pv`; the weaker exported final theorem was removed. Its edge definition exactly matches the P9 hypothesis of R1884_1. All dependencies are inlined, import only Defs. 6862 lines,522915 bytes, SHA256 `3399cacfff74c94405a529bf6c1ac10962a91c63284413d0bd9b62278b77f347`. This renamed extraction has not been rebuilt; its baseline is the checked library source. At almost512KiB it leaves little space for a full proof, so integration needs certificate sharing/compression, not blind concatenation with another large certificate.

## Checked pivotality extraction

`Pivotal.lean` is the first Lean block from the complete public PR8799 JSON saved at `gap1884/library_route/pr8799.json`, with only namespace L_meta_999921 renamed to L_meta_1884.Pivotal and final theorem renamed Pivotal.statement. SHA256 `627593adb7a223fc78d0352b8fcb4edb439a61c48a7dbfedecc25e2fdb4c2d2d`. Compilation and olean export exited0; pivotal.stdout/stderr are empty. Reviewer independently checked all2640 pins. Integration must move the final statement alias inside the namespace or omit it and use pivotal_two: the frozen source's top-level qualified alias is rejected by the local placement guard. This finite result does not settle the circuit core.

## New checked monotone orbit

`TripleOrbit.lean` (78lines,3536bytes), SHA256 `b4c214ae0979536534021bc3a85bd3a7706e2c27161e7a236cb256bc6fdc0992`, compiles and exports with exit0. Complete triple-orbit.stdout contains six tactic-style linter warnings; stderr is empty. Development import PetersenGeometry refers to the frozen old2590 cache; all source prerequisites are archived. Namespace L_meta_1884.SixOrbit.

`triple_orbit_impossible` rules out a StrictLive correct Petersen monotone DAG of length≤18 whose ineligible vertices are exactly{1,3,5}. For T={0,2,8}, its three ineligible neighborhoods give two overlapping support pairs and force Bplus≥9. The total surplus budget≤9 then forces Bzero=0. Consequently the ineligible vertices have unique chains to the output. The existing exact-neighborhood lemma produces all three distinct2-element supports on T. `tri_occ` forces Bplus≥10, contradiction.

The empty-ineligible case already follows from10 eligible vertices and totalSurplus≤9. Remaining canonical I={0},{0,2},{1,4,5},{2,4,5,6} are not closed here. Reduction_strategy owns the last orbit.

## Remaining structural obstruction

For I={0}, the basic triple bound is tight at9, yielding Bzero=0 and no residual units. It does not itself contradict the graph. A static consumption-code configuration can encode the central star, three spoke stars, and a large K3,3 rectangle on the remaining6-cycle, satisfying support/cover-free bookkeeping but admitting false-positive opposite pairs. Excluding it requires a DAG-order or semantic-filtering argument. For I={0,2}, the independent saturated triples are{1,4,7} and{1,5,3}; the superficially similar{1,4,3} is not independent and must not be used.

## Second checked monotone orbit

`PairOrbit.lean` (206lines,10308bytes), SHA256 `5ebc0525ea526f94ba0fb17e7d01a480c98291a71f8784b13a79ebd92a1d3af8`, compiles/exports with exit0 and empty complete pair-orbit.stdout/stderr. It imports cached PetersenGeometry. `pair_orbit_impossible` excludes StrictLive correct Petersen DAGs of length≤18 with ineligible set{0,2}. The copied 31-line two-ineligible-neighbor lemma comes from the frozen old FourOrbitCodes source; other proof code is new.

The two independent triples{1,4,7} and{1,3,5} saturate the budget. `tri_sat` forbids their appearing as full supports. The common-terminal lemma applied to vertex1 and vertex3 or4, combined with cover-freeness, forces the latter two consumption codes to have size≤2. Their private slots must pair to realize edge3–4. The same private slot for3 must then realize edge3–8, contradicting privacy for4.

The new `common_code_obstruction` helper may be useful for other orbits: under exactly one residual unit, a heavy code x with a slot containing a but not c cannot share two common terminals with a heavy code c if c–a is a nonedge. Cover-freeness gives the contradiction.

Remaining canonical nonempty orbits are I={0}, maximal triple{1,4,5}, and I4={2,4,5,6}. A proposed I1 three-dead-gate restriction argument is UNPROVED: singleton support{0} does not imply the consumer operand equals the variable x0, since higher-degree empty-support terms can join it. Therefore settingx0=0 does not automatically kill that consumer. No checked orbit proof above uses this assumption.

## Preservation at the L1884 stop

All mathematical work stopped upon the parent's STOP notification. No compiler remains active. The reduction agent separately completed the I4 orbit; the maximal-I3 orbit below is not yet closed.

- `MaxTriplePrelude.lean`,78lines, SHA256 `c89c83a13e5b8bcb577959b1c3ce0116cbda7b33f50f35147d6f35b4369ddbad`, is a frozen checked prefix. Full `max-triple-prelude.stdout` and `.stderr` are empty. It defines Simple as having at most one consumption slot whose source omits pivot0, and derives this condition from a saturated set of pivot-carrying slots, an empty residual profile, or profile inclusion in the pivot profile.
- `MaxTriple.lean`,335lines, SHA256 `746735fa89c9094d8280a7c5f05592a772ad4635119d804e7f57bde657312f5b`, and its exported olean completed with exit0 before STOP. Complete `max-triple-5.stdout` and `.stderr` are empty. Imports are cached I4Bridge and PairOrbit; their source prerequisites must be inlined for a submission. It proves the residual budget≤2 and a nonempty pivot profile for maximal I={1,4,5}; all nonsimple outside labels have the same singleton residual profile and share one ineligible neighbor. If a nonsimple label exists, pivot0 has exactly its three assigned slots and no carrier merge. This is a structural partial, not the orbit contradiction.
- `MaxTripleFinish.lean`,76lines, SHA256 `4815457a988ebb8ac2c2a70f183f2136076bd5eae0da062e53f9c4ebdc948626`, is an UNCOMPILED draft. Its first theorem attempts to combine the checked profile classification with lower_bound's checked SimpleAdjacency lemma to show every outside label is Simple. Its second theorem is an abstract C6 counting argument: six singleton private slots cannot realize every C6 edge by barred pairing, with at most one exceptional pivot exit whose opposite source is a singleton endpoint. Neither draft theorem has been checked.

The missing bridge at STOP is lower_bound's stronger earliest-meeting argument on support{0,c,d}. It would connect an eligible edge to paired pure slots or to the one exceptional pivot exit. Simple adjacency alone is not sufficient: an AND gate can initially preserve the pivot, so direct application of ordinary edge slots is invalid without additional pivot-exit/merge premises. The checked profile partial does not use that invalid shortcut.
