# L-meta-949 orchestration notes

Assignment: 2026-11-25 10:24:25 UTC. Task is a REDUCTION, explicitly not a proof. Only root holds and renews the known lease. No agent may call the desk, push, commit, or create a PR.

Target: existence of a six-vertex graph whose partial-function AND-count circuit has fewer gates than its biclique cover number. Desk allows reductions; one is already live. Need 2–4 genuinely smaller, plausible hypotheses, checked on finite cases before submission. Main theorem must exactly conclude the posted statement.

Read `/tmp/oec/pequalnp-pilot-82/assignment.json` for the full statement and context, after discovering it. Shared lemma attempts belong in `results/orch/lemmas/`; assign unique filenames. Record findings here with UTC timestamps. Do not overwrite another agent's notes.

Environment: upstream c0a34c73, Lean 4.36.0 installed at `/tmp/oec/pequalnp-pilot-82/elan`. Set `ELAN_HOME` to that path and invoke its `bin/lake` explicitly. Full Mathlib cache exhausted the 7.9 GB disk; its generated Mathlib module artifacts were removed. Root is arranging a minimal cache. Do not start competing full cache downloads or build Mathlib from source.

Rules: no sorry, new axioms, native_decide, _root_, quotes, forbidden commands/attributes. Reduction file has only approved imports and ONE fully named top-level theorem, no namespaces or other declarations. Final PR diff must add exactly one Lean file. Scratch and evidence will be preserved on branch history and removed from the final PR diff.

## Independent reduction review (2026-11-25 10:25:52 UTC)

Existing R_meta_949_1 is mathematically unusable: its universal hLower is false. Take the empty graph and C = AndCountCircuit.starCircuit G empty. The circuit has size 0, empty output, and is well formed. The only maximal independent set is the full vertex set; evaluation is false and the outside-vertex extension condition is vacuous. A cover by zero bicliques exists, contradicting hLower. Never promote a merely checker-accepted cut without auditing the hypotheses.

Preferred smaller cut, once a finite candidate G and bound k are found: (1) construct a circuit C of size at most k satisfying the partial function condition for that fixed G; (2) prove no cover of that fixed G has at most k bicliques. A third child may isolate the finite maximal-independent-set classification used to verify C. Each child must be independently checked for plausibility; the lower-bound child must not quantify over all well-formed partial circuits as the existing reduction does.

Current checker: reduce conclusion must be structurally equal to the posted statement, with 2 to 4 independent closed proposition hypotheses; no helper declarations or namespace. All hypotheses use only Mathlib/Defs symbols, no target as a subterm, no duplicates, no False or decidably false child, no text/meta types, at most 2000 printed characters each. Use exact posted conclusion bytes and explicit kind reduce for both guard and checker.

## Finite search 2026-11-25T10:27:15.902937+00:00

Exact unlabeled graph enumeration gave counts 1,2,4,11,34,156 for n=1..6. Enumerated every biclique and exact minimum cover. Six-vertex cover histogram: 0:1, 1:9, 2:61, 3:80, 4:5. For all 155 nonempty graph representatives, CaDiCaL returned UNSAT for the full partial-function circuit synthesis at one fewer AND gate than the cover number. The five bc=4 graphs all rejected 3 gates in under 0.2 seconds. This is evidence the existential target is false, not a Lean refutation. Positive control: all 156 graphs SAT with exactly bc(G) gates, and each solver witness reevaluated against every maximal-independent and one-extension input. Source `results/orch/lemmas/search_949.py`; complete results `/tmp/oec/pequalnp-pilot-82/finite-search/results6.json`, complete diagnostic logs `/tmp/oec/pequalnp-pilot-82/finite-search.log` and `finite-validation.log`. Seven-vertex search underway to reproduce expected separation and further validate encoding.

## Lean reduction agent 2026-11-25T10:29:04.630358+00:00

Existing R_meta_949_1 hLower is false: the empty graph and its zero-gate star circuit satisfy the partial condition and have an empty biclique cover. Source proving the exact negation is in lemmas/lean_existing_cut_counterexample.lean. Initial compilation is blocked only by missing project AndCountCircuit.olean, which root is building.
Positive-reduction bridge is straightforward once a real graph witness exists: a fixed graph circuit-existence hypothesis with size ≤ k and a separate biclique-cover lower bound > k. Exact SAT search currently reports all156 representatives UNSAT below their biclique cover counts, so no such true hypotheses are presently supported.

2026-11-25T10:29:56.855308+00:00 lean_reduction: `lemmas/lean_existing_cut_counterexample.lean` compiled via `lake env lean`, exit0, empty stdout/stderr. It proves the exact negation of existing R_meta_949_1 hLower. This is a checked flaw in that previous reduction, NOT a checked refutation of L-meta-949. Root notified immediately for independent review and push preservation.

## Independent semantic enumeration (2026-11-25T10:30:04.884990+00:00)

A second implementation, without CNF or a SAT solver, confirms there is no circuit with fewer AND gates than the biclique cover number for any graph on six vertices. `results/orch/lemmas/sat_enum.cpp` evaluates gate signatures on maximal independent sets and their one-vertex extensions. For the last AND gate, it enumerates complementary partitions of the negative examples and maximizes each OR side over signals whose negative footprint lies inside its part. A candidate exists exactly when both maximal sides cover every positive example not already covered by safe earlier output gates.

All 155 nonempty isomorphism representatives returned UNSAT at bc(G)-1. The five graphs with biclique cover number 4 required between 757078 and 1144038 enumerated two-gate prefix signatures each; all were exhausted. Positive controls at bc(G) succeeded for every one of the 151 representatives with bc(G) ≤ 3. Full logs are `/tmp/oec/pequalnp-pilot-82/sat-enum.log` and `sat-positive.log`.

`results/orch/lemmas/sat_audit.py` independently confirmed the graph census: the 156 representatives have disjoint relabeling orbits covering all 32768 labeled graphs. It also recomputed every biclique cover number by a separate maximal-biclique/first-uncovered-edge recursion. Full log: `/tmp/oec/pequalnp-pilot-82/sat-audit.log`.

This is rigorous finite computational evidence, independently implemented, but is NOT yet a Lean-checked refutation. The target appears false, so a reduction into all true hypotheses cannot exist.

### Additional independent controls 2026-11-25T10:30:07.524896+00:00

All n≤4 cases were exhaustively enumerated directly, including output bare variables, and agreed with SAT. All156 n6 graphs had SAT witnesses at exactly their biclique-cover numbers; every witness independently evaluated. At n7 the first bc5 graph (mask450097) admits4 AND gates; the first bc4 graph (mask2060156) admits3 AND gates. Thus the known seven-vertex separation is reproduced, and no universal ≤3-gate equivalence theorem can prove the n6 result. Complete source/results/controls copied into results/orch/lemmas/search_949*.
Proof-certificate experiment: five hard n6 bc4 graph LRAT refutations are all RUP,0.8–1.2MB each, and backward trimming leaves0.56–0.87MB each. Direct embedding of all certificates exceeds the512KiB file limit. A semantic finite-state solver bridge or additional compression/normalization would be needed for a complete Lean refutation.

## Preservation-push independent review (2026-11-25 10:30:25 UTC)

Reviewed exact Lean partial source SHA256 59cf22e1770d7a968a80b1f266352b071204a4fdfc242f27939b91f2b036b8cf. The theorem refutes the universal lower-bound hypothesis of prior R_meta_949_1, not the original L-meta-949 target. Empty graph, zero-gate circuit, and zero-biclique cover argument is sound; source has no forbidden proof placeholders or unsafe/native constructs. Build result still required before labeling it Lean-checked.

Inspected all three Python research scripts, finite result shapes, and search logs; no network activity, credential reads, or credential-pattern matches found in results/orch. The SAT encoding allows arbitrary gate sides and previous-gate reuse. Excluding bare output vertices is mathematically justified because every vertex lies in some maximal independent set; testing one gate fewer suffices for all smaller sizes by padding dead gates. Six-vertex records: 155 UNSAT, one empty graph untested; seven-vertex records: one SAT witness, 1043 untested. No claim of a Lean refutation of L-meta-949 is justified by these finite solver results alone. No content blocker for a preservation push, provided the compile succeeds.

- 2026-11-25T10:30:54.866108+00:00: structural_route: existing R_meta_949_1 lower hypothesis is false (ordinary edge-computing circuits refute it). Developed a generic ≤2-AND argument through maximal false sets; formalizing its graph component: any graph whose independent sets are all contained in three independent sets admits a two-biclique cover. Source results/orch/lemmas/structural_three_mis.lean. A genuinely nested two-AND function has at most three maximal false sets; depth-one case has at most four, and if all four are graph MIS it computes the exact edge function.

- 2026-11-25T10:32:19.608410+00:00: structural_route: structural_three_mis.lean compiled with Lean exit0, full log structural-three-mis-4.log (only push_neg deprecation). Independently checked upstream L_meta_950 final theorem: it is the exact universal negation of posted L-meta-949 existential, with identical WellFormed and maximal-independent-set partial conditions and identical cover existential. Thus the assigned positive reduction task is stale and false.

## Prior checked theorem located 2026-11-25T10:32:29.882737+00:00

Root found `lean/PEqualNP/Outside/L_meta_950.lean`, whose final theorem is exactly the universal negation of L-meta-949. Independent public-feed check confirms L-meta-950 is already CHECKED, credited to sanchan. The local file SHA256 matches the public checked record exactly: 0b7e2f524d8cf838ed8e00ccb86224d0fa9ba587dfb9e5f750c1325d73a4cc3a. Upstream commit fcb70f4f1f62682f6d680290de26bfa5a1fc2f7b, PR1995. All new searches stopped. Root will reproduce a selfcontained refutation for preservation; no positive reduction with plausible hypotheses exists.

## Structural partial and stale-target review (2026-11-25 10:32:32 UTC)

Independent review passed for structural_three_mis.lean, SHA256 40ce9b1f13ebd3d732cff91083ec5e84967cd0f87b3dfd2acdffd0271904022a. It proves a graph whose independent sets are covered by three independent sets has a two-biclique cover, by showing one pair-membership class must be absent. No forbidden source markers. Reported exit-0 compilation log has only a push_neg deprecation warning. Safe to preserve; do not stage generated __pycache__.

CRITICAL: upstream L_meta_950 main theorem universally supplies exactly the cover forbidden by the posted L-meta-949 statement, under exactly its WellFormed and partial-function conditions. Thus L_meta_950 mathematically refutes L-meta-949. The expected contradiction is obtain G,C,hw,hp,hn from the existential target, then apply hn to L_meta_950 G C (hw,hp). Because the desk permits only PEqualNP.Defs, importing L_meta_950 would violate its import list; the self-contained copied proof route must still compile and satisfy source/checker rules before a final result claim.

## Existing opposite theorem audited (2026-11-25T10:32:33.224669+00:00)

`lean/PEqualNP/Outside/L_meta_950.lean` already states the exact universal opposite of L-meta-949: every well-formed six-vertex partial-function AND-count circuit admits a biclique cover of size at most its AND count. A mechanical string comparison confirmed that both the partial-function clause and the biclique-cover clause are byte-for-byte equal to the corresponding clauses in the desk assignment, with the same Fin 6 domains. Only logical quantifier/implication packaging differs. Source size: 193409 bytes, 3465 lines. Its argument is structural (circuit sizes 0, 1, 2, 3, and universal cover bound 4), not a SAT certificate. Root is compiling the self-contained refutation. New certificate work stopped.

## Full refutation provenance 2026-11-25T10:33:08.126172+00:00

`lemmas/lean_full_refutation.lean` is adapted from upstream `lean/PEqualNP/Outside/L_meta_950.lean`, commit `fcb70f4f1f62682f6d680290de26bfa5a1fc2f7b`, PR #1995, author sanchan (2026-11-24). The 3465-line upstream proof is NOT new work by this pilot. Changes: minimal tactic imports instead of all Mathlib; helper namespace renamed; prior universal theorem made helper lemma coverBound; final theorem negates the EXACT L-meta-949 desk statement. This directly documents that the desk assigned a stale false positive target. Local compilation in progress.

2026-11-25T10:33:45.564879+00:00 lean_reduction: FULL EXACT REFUTATION COMPILED. `lemmas/lean_full_refutation.lean` (3472lines) passed `lake env lean`, exit0. Compiler output is 7173bytes of upstream deprecation warnings only, retained in `/tmp/oec/pequalnp-pilot-82/lean-full-refutation.log`. Final theorem `PEqualNP.Outside.L_meta_949` proves `¬ (` plus the exact assignment statement plus `)`. Root notified immediately for review, checker, and preservation push.

## Full-refutation independent review (2026-11-25 10:34:26 UTC)

PASSED preservation review for lean_full_refutation.lean, SHA256 c42c21625e76882b761201bbeaf188ae145111c385c21cb4ae2518537b302335, 3472 lines, 194242 bytes. Diff against upstream L_meta_950 contains only narrower Mathlib imports, helper namespace rename, conversion of its main theorem to coverBound inside the helper namespace, and the final contradiction theorem. Automated byte-string comparison confirms its theorem states exactly the negation of assignment.gap.statement. The compile log contains deprecation warnings only. Independently ran current outside-guard checkProofFile against the assignment import list and PEqualNP.Outside.L_meta_949: all text, import, and namespace checks passed. The official local checker verdict is still a separate required result.

## Final preservation artifact review (2026-11-25 10:36:23 UTC)

No blockers in remaining sat_enum.cpp/search_949.py changes or new provenance/control logs. The C++ change asserts its intended six-vertex, at-most-three-gate scope. Python extensions add optional side symmetry, last-output selection, custom tests, and tagged filenames without changing default census behavior. Provenance SHA256 matches upstream L_meta_950; local git identifies commit fcb70f4f1f62682f6d680290de26bfa5a1fc2f7b as L-meta-950 (#1995). New seven-vertex logs contain one three-gate SAT witness and 650 selected two-gate UNSAT cases, not an unrestricted seven-vertex circuit census. Credential-pattern scan of 26 research/source/log files found no matches. Generated __pycache__ is excluded. Final report must distinguish successful named lake build from local checker FAULT exit 3 due to missing prebuilt Batteries.olean; no ACCEPTED verdict was obtained.
