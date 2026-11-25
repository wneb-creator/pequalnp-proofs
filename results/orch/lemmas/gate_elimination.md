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

Second bounded evolutionary trial completed:120.001 seconds,416,234 mutations,46 restarts,58,381 distinct labelled valid graph outputs; no positive-gain witness. Best valid output has16 edges, minimum cover6,21 reachable gates. The independent scalar Boolean verifier again checked every16,384 input assignment and directly enumerated minimum covers. Complete artifacts: `evolve_graphs_v2.py`, `evolution-v2-3566.json`, `evolution-v2-3566.log`, `evolution-v2-3566-verified.log`, in the same scratch directory. Counts from the two trials are not deduplicated across trials.

The revised search still drifts to smaller graphs despite a soft size penalty. `evolve_fano_prepared.py` is prepared but not launched: random relabelings of the7-by7 Fano incidence graph (rows i+{0,1,3} modulo7),27-gate star circuits, a hard18-edge minimum, exact truth-function wire merging, and the same full truth-table checks. This targets the smallest possible minimum-degree-three regime: no-four-cycles plus minimum degree3 forces each side to have at least1+3*2=7 vertices. All searches remained single-worker jobs coordinated with certificate_search and finite_search.


Fano trial completed120.001 seconds,248,838 mutations,51 restarts,27,341 distinct labelled valid outputs; no counterexample. Under the hard18-edge floor, there were21 distinct numeric circuit-form signatures, only2 with dirty ANDs and none with dirty ANDs at the cover-bound optimum. Best valid remains the21-edge Fano graph at27 gates; scalar verification independently checked all16,384 assignments and minimum cover7.

At115.6 seconds the search found an18-edge graph of minimum cover7 computed with25 gates, one above the24-gate cover upper bound, with one dirty AND. The independent verifier confirmed the function and dirty gate on every assignment. Inspection shows this is trivial absorption: the dirty subcircuit is `(x5 AND (x8 OR x13)) AND x8`, equivalent to the one-gate edge `x5 AND x8`; vertex5 has degree1. Thus the late improvement is not a promising new form.

Recommendation: do not spend10 minutes extending the unchanged search, which visibly moves between clean optimal star forms and redundant dirty encodings. A useful prerequisite is exact replacement of intermediate functions equal to a one-gate AND/OR of original inputs; `evolve_fano_resynth_prepared.py` adds this and is prepared but unrun. More meaningful exploration would require deliberately seeded nontrivial dirty factorizations or coordinated algebraic mutation, rather than more random gate edits.

Complete Fano artifacts in the same scratch directory: `evolve_fano_prepared.py`, `evolution-fano-10760.json`, `evolution-fano-10760.log`, `evolution-fano-diagnostics.json`, `evolution-fano-best-dirty.json`, `evolution-fano-best-dirty-verified.log`, `evolution-fano-best-verified.log`, `evolution-fano-dirty-structure.txt`. The CPU slot was released to certificate_search for its C8 helper DP.


## Deliberately dirty seeds with semantic shortcuts

Added a table of exact one-gate AND/OR truth functions of original inputs to the simplifier, then pruned again; this removes the earlier absorbed-leaf artifact. The new seed construction starts from Fano rows a,b with unique shared neighbor d, retains all other five rows, trims b to {d}, and keeps either {c,d} or {c,e,d} at a. The a/b contribution is computed as `(a OR b) AND (C OR d) AND (a OR d)`, with C=c or c OR e. This is a genuine dirty P4/double-star factorization, exactly one gate above its cover bound; the graph has18 or19 edges, minimum cover7. The seed circuit is shuffled topologically, preserving the output at the end. A bounded dirty-form novelty bonus encourages exploration without changing the exact feasibility/witness test.

`evolve_dirty_seeds.py` trial:180.001 seconds,667,081 mutations,71 restarts,49,124 distinct labelled valid graph outputs. No counterexample. Restricting diagnostics to graphs with at least18 edges gives9 numeric form signatures,7 dirty, none dirty at the cover bound. Closest dirty signatures are (18 edges, cover7,25 gates) and (19 edges, cover7,26 gates), exactly the one-gate overhead seeded initially. The best clean graph has18 edges, cover6,23 gates, meeting its upper bound.

Independent scalar verification checked all16,384 assignments, minimum cover by direct subset enumeration, and dirty AND predicates for both saved candidates. The best dirty gate is `(x0 OR x6) AND (x10 OR x11 OR x12)`, true at the nonedge {6,10}; the output filters the extra pairs. This is not the previously absorbed leaf expression, but it does not improve on the seeded template. The unchanged algorithm therefore still lacks evidence justifying a long run.

Complete artifacts in the same scratch directory: `evolve_dirty_seeds.py`, `evolution-dirty-3566179.json`, `evolution-dirty-3566179.log`, `evolution-dirty-diagnostics.json`, `evolution-dirty-best.json`, `evolution-dirty-best-verified.log`, `evolution-dirty-clean-verified.log`, and `evolution-dirty-best-structure.txt`. The CPU slot was handed to certificate_search for its180-second C8 helper sweep.


## Reusable-helper amplification audit

Implemented callable `audit_case(n, edges, gates, output=None, subset_budget_s=0.5, build_extension=True)` in `reusable_helpers.py`. It verifies the original complete truth table, applies exact duplicate-function/input-pair shortcuts, computes every existing wire's singleton support, and checks same-side compatibility, absence of a common old neighbor for any support pair, and `OR(S) <= h <= OR(S) OR F` on the full truth mask. It permits disconnected component flips, then verifies joint bipartiteness of each whole proposed extension. Pairwise support intersections must have size at most one. Unused helpers are charged by the union of their gate cones and the output cone. Compatible subsets are scored by `m+tau-1 + sum(|S|-1) - cone_union_size`. Any positive subset is assembled with fresh centers/private leaves and all gate indices shifted correctly, then checked against its complete extended truth table before being returned.

Audited29 distinct saved full circuits: evolution raw and normalized records, every finite_search witness, and the two canonical certificate_search full-circuit records. All29 passed full truth verification; all subset searches completed. Only3 circuits had safe supports of size at least2. Every such helper was an unused input OR whose extra gate exactly canceled its extension benefit; no profitable subset. The support audit correctly found cross-seed-color supports spanning disconnected components, while the final extension test enforced jointly consistent component flips. Certificate_search received the reusable scorer for discarded/growing extractor candidates and was asked to adapt saved C8 free-helper DP files into actual circuits before auditing them.

Controls: reconstructed the known C8 unused-helper extension with15 gates,11 edges,minimum cover5 on10 inputs; independent scalar verification checked all1,024 assignments. A separate graph with two components supplied two individually legal helper supports whose flips conflict jointly; the combined extension was rejected as non-bipartite.

Artifacts in the same scratch directory: `reusable_helpers.py`, `helper-audit-files.txt`, `helper-audit-results.json`, `helper-audit.log`, `test_reusable_helpers.py`, `helper-audit-tests.log`, `helper-extension-positive-control.json`, `helper-extension-positive-control-verified.log`. No new heavy mutation run was launched for this task.

Extended the amplification audit to certificate_search's saved free-helper DP outputs by explicitly prepending their helper circuits and preserving the wire offsets. First batch:2,130 distinct reconstructed circuits (65 one-helper cases plus the two parts of the2–3-gate helper sweep), all256-row truth tables correct;262 had multiple safe helpers; maximum amplification profit0. Second batch:110 all-safe-prefix circuits, all full truth checks correct, maximum amplification profit0. No positive compatible subset occurred. Audit runtimes were0.87 and0.10 seconds respectively, so this was a cheap saved-artifact pass.

Additional artifacts: `audit_helper_dp.py`, `helper-dp-audit-results.json`, `helper-dp-audit.log`, `helper-all-safe-audit-results.json`, `helper-all-safe-audit.log`, plus the complete filename-discovery manifests. Certificate_search now has the callable scorer for live extraction objectives.


## Pendant-leaf amplification and combined audits

Implemented `pendant_helpers.py`: finds AND gates with an OR-only path to the output and an operand equal to an original input, or with singleton support {v} and function bounded by x_v OR F. Enumerates at most4 distinct centers and requires an injective assignment to distinct target AND gates, selecting at most one operand per gate. It computes the exact augmented matching number, inserts the fresh-leaf OR gates with corrected indices, and fully checks any positive extension.

Audited all2,269 saved full/reconstructed circuit records in0.94 seconds: all original truth tables correct;118 have generalized nonlinear singleton operands;393 admit a positive cover rise, but no cover rise exceeds the circuit deficit. `audit_combined_extensions.py` then preserves every canonical old wire, performs the best pendant edits, and reruns reusable-helper/cone-union amplification. All393 combined circuits passed full truth verification; maximum combined profit0.

Controls included a14-gate pendant extension on10 inputs, independently verified on all1,024 rows with10 edges and minimum cover5, and a genuinely nonlinear singleton-operand insertion, independently verified on all512 rows. The latter control retained dirty gates, so it tests the generalized condition rather than only a literal-input special case.

Artifacts: `pendant_helpers.py`, `pendant-audit-results.json`, `pendant-audit.log`, `audit_combined_extensions.py`, `combined-extension-audit-results.json`, `combined-extension-audit.log`, `pendant-positive-control.json`, `pendant-positive-control-verified.log`, `pendant-generalized-control.json`, `pendant-generalized-control-verified.log`.

## Amplification-objective reverse search

Prepared `evolve_amplification.py`, reusing each candidate's full truth values and gate cones. A cheap screen charges helper i only its unique gates H_i minus the union of the output cone and every other helper cone. The sum of positive weight-minus-unique-cost terms is an optimistic upper bound; only potential improvements trigger the complete compatible-subset audit. This skips unused ORs that merely pay for themselves. Every positive objective requires the constructed extended circuit and graph to pass full verification. The archive retains circuits according to amplification profit, allowing positive base overhead when useful existing signals offset it.

The screen agreed with full audits on14 seeds, including8 reconstructed C8 circuits containing used safe helpers. A180-second trial, seed3566180, was launched after certificate_search released its CPU slot. Its edge floor is8 so those C8 signals remain eligible; Fano-derived seeds are also included. Pending artifacts: `evolution-amplification-3566180.json` and `.log`; validation is `evolution-amplification-validation.json` and `.log`.

### Amplification-objective evolution trial

The 180-second trial (seed 3566180) evaluated 260,997 circuits, with 114,088 valid visits across 43,792 labelled graphs. It encountered 79,272 safe-helper cases and ran 16,183 full compatible-subset audits, all complete. No positive amplification profit was found. The saved best is the 21-edge Fano graph with cover 7 and 27 gates; independent scalar verification checked all 16,384 rows and direct minimum-cover enumeration. Its pendant cover rise is zero. Full artifacts: `evolution-amplification-3566180.json`, `.log`, `-verified.log`, and `-pendant.json` in the gate_elimination scratch directory.

A combined objective is prepared in `evolve_combined.py`: it adds the exact best pendant cover rise from at most four eligible distinct centers to the safe-helper profit. It screens with the cover rise from all eligible centers, then solves the small distinct-target-gate assignment problem. Positive candidates must be physically transformed and pass the full extended graph/circuit audit. Validation agrees with the standalone helper and pendant audits on 22 seeds, including eight circuits with positive pendant cover rise; each transformed validation seed passes a full truth-table audit. Validation artifacts are `evolution-combined-validation.json` and `.log`. No combined mutation worker has been started yet.

Independent reviewer `repo_review` confirmed the cheap unique-cone-cost screen: for selected helpers I, incremental cone cost is at least the sum of their disjoint gates that occur in no other helper or output cone. Therefore base profit plus the sum of positive (helper weight minus unique-gate cost) over all helpers is an upper bound. Ignoring compatibility and all shared costs can only enlarge it.
