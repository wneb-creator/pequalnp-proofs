# Gate elimination route

Explored independently for L-meta-10760 on 2026-11-25.

## Reusable formal lemmas

`lean/PEqualNP/Outside/L_meta_927.lean` has a self-contained simplification/relabeling/gate elimination framework in lines 1–1124. Relevant final lemmas:

- `one_gate_at` (1041): for an essential variable p and nonconstant restriction f[p:=b], a circuit of size s yields a circuit for the restriction of size at most s-1.
- `gate_elim_at` (1083): if both restrictions are nonconstant, one of the two has a circuit at most s-2.
- `dep_lower_set` (170): dependence on k variables needs at least k-1 gates.

These lemmas cover unrestricted AND/OR/NOT circuits, so they are sound lower-bound tools for this task. They cannot be imported directly; helpers must be copied under the target namespace.

## Computed strength and limit

A dynamic program applying dependency bound, fixed-value elimination, and two-gate branching to every partial assignment found a lower bound of only 8 (344 restriction states).

Exact biclique-cover formula DP gives the following upper bounds on the seven zero restrictions:

| removed input | monotone upper bound |
|---|---:|
| 0 | 10 |
| 1 | 10 |
| 2 | 10 |
| 3 | 10 |
| 4 | 10 |
| 5 | 10 |
| 6 | 9 |

Consequently, even exact six-variable base lower bounds cannot make a simple one-gate elimination reach beyond 11. The two-gate branch is still weaker because f[p:=1] has many singleton minterms. This route alone cannot establish the current 14-gate upper bound.

## Structural observation about the single NOT

The complement graph has no triangle. Its nine edges (the target graph nonedges) are:

[(0, 1), (0, 3), (1, 2), (1, 6), (2, 3), (2, 5), (3, 4), (4, 5), (4, 6)]

Hence the graph has independence number 2. Its edge function is true on every assignment with at least three true bits and false on exactly 17 inputs (empty, 7 singleton inputs, and 9 nonedge pairs).

Let u be the monotone function entering the only NOT. If u ≤ f pointwise, replacing that NOT by a constant-true AND gate yields a same-length monotone circuit computing f. Indeed, where u=false the replacement does not change the NOT output; where u=true the original output already equals true, and the monotone suffix can only increase when the NOT output rises from false to true.

Thus any genuinely essential NOT for this f has u=true on an independent set of size at most 2. This reduces the hard structural cases to singleton or nonedge-pair witnesses, but I do not yet have a complete size-preserving simplification for those cases. Do not assume a general one-NOT elimination theorem.

Scratch DP: `/tmp/oec/pequalnp-pilot-178/gate_elimination/basic.py`.

## Independent review of the 13-gate lower-bound candidate

Reviewed `/tmp/oec/pequalnp-pilot-178/certificate_search/Lower13.lean`, 3787 lines, 223078 bytes, SHA256 `139aa8ff86fa6f697837a4a6e8832ba5203acbb98efaa15cec5b56cd10130900`.

Verdict: no semantic loophole found; acceptable as a partial lower bound conditional on its Lean/kernel checks succeeding. No build was started by this reviewer.

- Independently diffed it against accepted `L_meta_10762.lean`. The generic proof engine and circuit bridge are unchanged. Changes consist of namespace, generated constants, certificate bound layers, explicit names for two noncomputable sections, target graph expressions, and the final lower13 helper.
- Independently decoded all large decimal limb expressions. They match the data JSON exactly.
- Independently checked all 820 used row bits against the exact target edge function. Every target bit agrees.
- Verified all 42 X and 17 Y segments have constant source assignments, valid zero boundary bits, and the correct HX/HY carry markers.
- The `f` and `EF` expressions use exactly edges 02,13,04,14,24,05,15,35,06,26,36,56.
- The bridge quantifies over the real project Circuit and FanInTwo definitions and maps actual circuit evaluation to the sample model. The conclusion is 13 ≤ D.size with only fan-in-two legality and target-computation hypotheses.
- No `_root_`, quotes, `sorry`, `native_decide`, axiom/unsafe declarations, prohibited commands, attributes, or decimal numeral longer than 20 digits found.
- The final posted replacement theorem is absent. This file is a partial lower-bound component, not a complete proof of the leased statement.

The prior suspected delete0 bound11 was indeed invalid: a concrete monotone10gate restriction witness is `(x3∨x5)(x1∨x6) ∨ x1x4 ∨ x2(x4∨x6) ∨ x3x5`. Sent its explicit gate list to certificate_search to diagnose the Python port. Current Lower13 bound layer uses10 for that restriction.

## Independent review of unique_not_count

Reviewed root helper `/tmp/oec/pequalnp-pilot-178/root_helpers/NotCount.lean`, SHA256 `8431b42887b252cfb9216e36ec7d64c295921c84dd5799d8f18263b73e701529`. Verdict: PASS. The count definition matches the tracked bridge. Indexed uniqueness is exactly the posted assumption. A NOT at the list head rules out all tail NOT positions by contradiction between index zero and a successor; otherwise the induction passes uniqueness to the tail through Fin.succ injectivity. Repeated equal Gate values are counted correctly because the assumption concerns positions. No extra hypotheses or unsafe declarations found. Root reported successful kernel compilation.

## Tracked gate/NOT extraction implemented and checked

Implemented 168-line supplement `/tmp/oec/pequalnp-pilot-178/gate_elimination/Tracked.lean`, SHA256 `66544a07b48f4a02189f5b76462caa054c364e92a6e67f20d9399e5ff513b671`.

- `SolCount` tracks concrete gate count q and NOT count n. Padding accounts for unused gates and semantically redundant/constant NOT gates.
- `SolCount.live` extracts Live k t S0 with t ≤ n and k + (n - t) ≤ q. Discarding a NOT therefore consumes one unit of the size gap.
- `notCount` is the requested List.countP of decide(op=not).
- `ex_solCount` proves the count-preserving abstract execution of the concrete circuit, including empty NOT gates and ignored extra NOT inputs.
- `bridgeCount` and `circuit_live_count` connect the actual circuit to the graph's sample engine.

Lightweight core compiled successfully, then the full supplement compiled successfully against the built target module. Both outputs were empty; both exit codes were zero. Preserved sources/logs: `results/orch/lemmas/TrackedCore.lean`, `results/orch/tracked-core-build.txt`, `results/orch/lemmas/TrackedFull.lean`, `results/orch/tracked-full-build.txt`.

Final deduction: if a concrete circuit has size≤13 and exactly one NOT, global lower13 forces extracted k≥13; k+(1−t)≤13 and t≤1 then give k=13,t=1. The new fixed-one-NOT checker endpoint excludes precisely this Live state. Original zero-NOT circuits can be returned unchanged, and circuits of size≥14 use the existing monotone14gate witness.

## Independent review of the assembled full candidate

Reviewed `/tmp/oec/pequalnp-pilot-178/root_helpers/FinalCutCandidate.lean`, SHA256 `afa12df79044cbf914ba884f1e47895742c7f8de9b1377da40c45acfc35120db`, 6977 lines / 507796 bytes. Verdict: conditional PASS, pending final frozen diff, successful named-file build, local checker, and recheck after computational rewrites.

- Final theorem statement matches the original desk JSON byte-for-byte.
- Final split is exhaustive: size≥14 uses the explicit witness; zero NOTs return the original circuit; otherwise indexed uniqueness gives exactly one NOT and tracked extraction contradicts the fixed-one-NOT certificate.
- Generic proof engine through one1 is token-equivalent to the previously reviewed Lower13 source (ignoring whitespace); no hidden assumptions were inserted.
- Sample constants are unchanged from independently verified data. The real circuit bridge retains actual root definitions, default-false nonexistent wire semantics, empty gate semantics, and correct NOT counting.
- `live_certificate_false` receives lower13 as minimality. It does not assume the desired14 lower bound or the target statement. The E=[] branch avoids the optional hypothesis for an extra precomputed input.
- Bucket lookup is conservative. `cutKey` is proved injective on the entire state, including every W field. `patchCut_eq` only replaces states whose original search result is already proved false. Hash collisions and missing bucket entries cannot introduce unsound pruning; unmatched entries evaluate the original search.
- The list of partition masks is verified complete by mFull. The two certificate arms cover the unary and binary root cases.
- Independently evaluated the explicit14-gate AND/OR witness on all128 assignments; every result equals the target graph function.
- Exactly one import occurrence, the allowed PEqualNP.Defs line. No forbidden strings, attributes, unsafe/axiom commands, hidden format/control characters, or oversized decimal numerals. All239 option lines use allowed forms.
- Candidate has16492 bytes of margin under the512KiB cap; recheck after further data representation changes.

No Lean process was started during this review.


## Gap L-meta-3566: restriction partial, 2026-11-25 20:54 UTC

Compiled `/tmp/oec/pequalnp-pilot-178/gap3566/gate_elimination/Restrict.lean` with the pinned Lean toolchain; exit 0. Complete output is `restrict-build-04.log` in the same directory (linter warnings only). SHA256: `63bee7161700d44108ca262d1938927c77568ee9cbdaa295930f60f6db72e9cc`.

The endpoint `PEqualNP.Outside.L_meta_3566.Restriction.graph_restrict_one_gate` proves that every positive-degree graph vertex whose incident-edge deletion leaves an edge admits a restricted circuit preserving the exact `IsAO2` model and saving at least one gate. The result needs neither bipartiteness nor the no-four-cycle assumption. Its deleted-graph Boolean function is spelled exactly as in the posted statement. It does not prove the degree-sized savings or the cover-drop bonus.

The generic `restrict_one_gate` also handles either Boolean restriction of any essential input whenever the restricted circuit function is nonconstant. The construction is the checked L-meta-927 simplifier, specialized to preserve AND/OR operators and exact fan-in two; temporary constant flags are `Sum Bool Nat` values only, and no constants or NOT gates enter the output circuit. A direct reader of the essential input must exist, otherwise input-support agreement contradicts dependence. That reader is omitted after constant propagation, yielding one gate of savings.

Independent red-team review of proof_route `Converse.lean` SHA256 `9841665b2baa990911687565525db2e7d9acd3eed7ce81c55a4cd14586a28a96` and root `PeelGlue.leanfrag` SHA256 `c299c0ea46fb84986d9b015c3722ab0ff51abcbc5ff71f96f3825fe3c17c8767`: PASS for the stated conditional implications, subject to the combined build. The graph-only witness is selected before the arbitrary circuit, deletion loses exactly degree many edges, and both directions account for the vertex-cover drop explicitly. The converse handles the empty residual graph by the singleton cover and the one-edge base by positive circuit size. Neither implication proves the posted assertion on its own; the exact monotone edge-plus-cover lower bound remains an explicit assumption. No custom graph semantics or hidden circuit-model relaxation found.


## Forest elimination extension review, 2026-11-25

Inspected L_meta_3525 `gate_elim_two` (line 885), `fix_many` (1113), and `claimQ` (1571); L_meta_1737 has the same mechanism. `gate_elim_two` is fully generic and guarantees two deleted gates for one of the two assignments, provided both cofactors remain nonconstant. The forest induction relies on a leaf whose neighbor has degree at most two, or on sibling leaves. The sibling case preserves cover number after one edge deletion; the low-degree-neighbor case balances the two-gate saving using an auxiliary singleton-input set A.

A bare even cycle already defeats a direct extension: for C6, potential |A|+|E|+tau begins at9. Setting a degree-two vertex false leaves P5, potential6 (drop3). Setting it true leaves two singleton neighbors and P3, potential5 (drop4). The primitive guarantees only2, independent of branch, so this argument cannot establish even the unicyclic case. Long ears attached to degree-three cores have the same local boundary-cost problem.

`fix_many` does not rescue this directly. It requires retained variables to stay essential under every assignment of the eliminated set L. If L contains an edge, the all-true assignment on that edge makes the output constant, so L must be independent. In triangle-free graphs, a retained vertex t is robust exactly when it has a neighbor u outside L with no neighbor in L: when t itself has not already become a singleton, u supplies a surviving edge. Thus most alternating-cycle eliminations destroy the required robustness.

Exhaustively checked the exact truth-table hypotheses (not only the graph criterion) for C6 and C8. The best `2*|L|+|T|` bounds on size+1 are7 and9, while the desired |E|+tau bounds are9 and12. Full diagnostic scripts and logs: `/tmp/oec/pequalnp-pilot-178/gap3566/gate_elimination/verify_fix_many.py`, `verify-fix-many.log`; graph-criterion enumeration through C16 is in `fix_many_cycles.py`, `fix-many-cycles.log`. This is a limitation of the direct use of these lemmas, not a counterexample to the posted claim. No heavy Lean build was run for this investigation.


## Reverse evolutionary circuit synthesis

Prepared `evolve_graphs.py`: circuits on14 inputs, fixed7+7 bipartition, exact Boolean truth masks on all16,384 assignments. The output graph is inferred from cross-pair evaluations. Feasibility checks include singleton and same-part pair outputs, every C4 corner pattern, and every extra true assignment outside the inferred edge function. The objective compares |E|+maximum-matching-size-1 with output-reachable gates; bipartiteness makes this the cover bound. Seeds are optimal15-edge5-by7 star circuits with19 gates and spare input vertices. Mutations vary gates and wire references, allowing the graph to change.

First bounded trial:120.002 seconds,776,482 mutations,50 restarts,10,340 distinct valid graph outputs; no counterexample. Best valid result retained15 edges, matching5,19 gates, gain0. Complete code/results/log: `/tmp/oec/pequalnp-pilot-178/gap3566/gate_elimination/evolve_graphs.py`, `evolution-178.json`, `evolution-178.log`. An independent Boolean-loop verifier checked all16,384 assignments of the best result, enumerated minimum covers directly, and confirmed gain0: `verify_evolution.py`, `evolution-178-verified.log`.

The first fitness underpenalized C4s relative to their legitimate circuit savings. Revised `evolve_graphs_v2.py` raises that penalty, merges exactly equal intermediate truth functions and serializes a pruned witness if found, and varies optimal19-to21-gate seeds across5,6,7 active left vertices. This second trial is queued behind certificate_search's extractor to respect the two-core limit.
