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
