# Final L-meta-3566 research checkpoint review

Independent reviewer: `repo_review`, 2026-11-25. **PASS for preservation and candidate validation. No proof or refutation of the posted theorem has been found.** This supplements `checkpoint-amplification-review.md` with the subsequently completed runs and relaxed-helper route.

## Relaxed-helper library and SAT model

Reviewed `gadget_helper_library.py`, `gadget_absorbed_library.py`, `gadget_relaxed_sat.py`, and the exact `subk33-absorbed-direct-library.json` proposed for the next bounded search. The immutable library SHA-256 is `f1bbff8ee3e0162e3241fbd1837e75806b1f73c350ae7b17eed24ae4d06a3ffe`.

The independent audit recomputed every recipe's Boolean sample signature and checked the entire union of recipe dependencies for cycles: 4,040 nodes, 6,181 recipes, maximum DAG depth 10. Thus adding absorbed helpers through direct single-edge clean nodes has not introduced a cycle. The direct-edge nodes cannot acquire later guarded recipes because those require support on at least two positive edge rows.

All 181 sample rows were checked. They contain all 50 maximal independent sets of the original graph, every singleton, and every maximal independent set of each graph induced outside a helper support. The latter counts are 8, 8, 29, 29, 29, 29, 29, 29. For a monotone helper h, true singleton rows on S imply OR(S) ≤ h. False maximal-independent rows outside S imply h ≤ OR(S) OR F: any assignment with neither S nor an edge extends to one of those rows. This proves the sampled helper criterion is sufficient, independently of semantic deduplication elsewhere in the library.

The eight supports have 10, 10, 13, 13, 13, 13, 13, 13 candidate nodes, totaling 98. Their candidate sets are disjoint: each candidate's singleton support is exactly S. Therefore the decoder's dictionary cannot silently combine observations from different supports. Exactly one selector per support is required; each selector forces its producing node and counts as an observed use. Gate charging remains one per selected noninput node plus the final output-term count. Emission subtracts one for the final OR tree, so raw gates are at most budget minus one; the chosen-helper overhead is 16, giving improving raw/paid bounds 38/22. Geometry and full truth-table absorption checks remain mandatory for every SAT witness.

Both P5 controls were independently checked on all 32 assignments, including each selected helper's two inequalities; each has raw size 6 and paid size 5. They are controls, not improvements. The independent script and full log are `gap3566/repo_review/audit_relaxed_library.py` and `relaxed-library-audit.log`.

The search is limited to the supplied recipe library and its retained recipes. An UNSAT or timed-out result is not an unrestricted circuit lower bound. At review time the new K3,3 relaxed query had not produced a result.

Reviewed source hashes:

- `gadget_helper_library.py`: `abbca4eb64f4780560dbf3afe22837a9bbdddcda6323ff32f146534295557deb`
- `gadget_absorbed_library.py`: `49a24d76315532a08200cc1602ec1e3894bc623446fdc9948f597bba9927ff15`
- `gadget_relaxed_sat.py`: `1cd01e5fa1d7a049d11c86f7e54193e3e5b435c0ce26ab7377f596a05b635242`

## Completed amplification records

All 59 paths in `gate_elimination/preservation-amplification.txt` exist. The previously approved main scorer and proof-condition source hashes are unchanged. New replay wrappers load the preserved seeds and cases without depending on the original exploratory directory layout.

Independent replay of the uncapped pendant audit reproduced all 2,269 distinct saved circuits, all 48,811 feasible center subsets, maximum eight eligible centers, and no pending cases. No circuit improved over the earlier four-center result; no counterexample was found. This removes the four-center cap for this particular saved corpus, not for arbitrary circuits.

The combined evolutionary trial completed in 180.000 s: 156,952 evaluations, 61,742 valid evaluations, 27,886 recorded graph keys, 7,169 complete helper audits, zero incomplete helper audits, and no witness. Its pendant-subset counter sums query results, including reused cached subproblems, and should not be presented as a count of distinct enumerations. Evolution remains heuristic.

All 288 recorded optimal pendant extensions were independently reconstructed. Each computes its exact extended graph function, has profit exactly zero, and has no dirty AND after the specified semantics-preserving normalization. The separate helper/combined materialization pass yields those same 288 pendant cases, zero new helper or combined cases, and 82 distinct mapped seeds. These observations do not prove that every optimal circuit can be normalized to clean AND gates.

The self-contained replay report contains all 2,269 saved cases, zero positive helper/pendant/combined results, and complete helper-subset audits for every recorded helper and combined case. The independent replay script and complete output are `gap3566/repo_review/audit_final_amplification.py` and `final-amplification-audit.log`; the latter records SHA-256 hashes of all 59 manifest files. The audit exited 0. No solver or Lean build was launched during this review.

## Checked symbolic upper control

`lean_setup/SymbolicLargeFast.lean` passed independent preservation review against its complete build log, `symbolic-large-control.json`, and `symbolic-large-simp-plan.json`. The source has 484 lines and 60,722 bytes; SHA-256 is `cfad2ef51ea932db37e91baad2da718aa9c0a9e84f93d49b012c90c1c6f1b50d`. The current generator reproduces it byte for byte. All circuit gates, input count, output index, and graph edges were independently extracted from Lean and matched to JSON. The generic circuit-evaluation and graph-evaluation bridges are unchanged from the previously reviewed generator.

The closed declarations prove exact AO2 membership, size 63, and `circuitFun 31 witnessCircuit = graphFun witnessGraph ∅`. The small base cut is proved algebraically, then rewritten into the full 31-input formula; precise distributivity simplification and associativity/commutativity establish the whole extension. There are no additional theorem hypotheses. Import and forbidden-format checks passed; only the permitted recursion/heartbeat limits occur.

Independent monotone-DNF normalization of all 63 gates yields exactly the graph's 50 minimal edge monomials, without enumerating 2^31 inputs. All 32,768 assignments of the 15-input base circuit and all eight exact OR helpers were also checked. The extended graph is bipartite and has no four-cycle; an explicit 14-vertex cover and 14-edge matching give minimum cover 14. Consequently 63 = 50 + 14 − 1: this is a known upper control and supplies no refutation or lower bound.

The full Lean log records exit 0, 16.136 s, maximum RSS 3,095,680 KiB, and six harmless unused-simp warnings. Independent audit script/log: `gap3566/repo_review/audit_symbolic_witness.py` and `symbolic-witness-audit.log`. Reviewed generator SHA-256: `703ca0c9e79f543ffc9787ca029e60ed0cab2487f38a59d991c6d5433704d3d0`; amplifier SHA-256: `3c7cb46d2dd6c32f7dfc2ba81dd7cdca06b5e56047afa44a998822e5375920de`. The amplifier currently supports exact OR helpers; relaxed helpers require their separate absorption argument and must not be treated as exact OR identities.
