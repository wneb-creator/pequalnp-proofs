# L-meta-10760 orchestration notes

Lease held only by root. Gap record and exact statement: /tmp/oec/pequalnp-pilot-182/desk-first.json and statement.txt. Allowed project module: PEqualNP.Defs. All helpers must merge into lean/PEqualNP/Outside/L_meta_10760.lean. No other existing files may change. Worktree updated to upstream 7a468ff1.

Graph edges: 02 13 04 14 24 05 15 35 06 26 36 56. Seven inputs; arbitrary AND/OR/NOT gates of fan-in at most two, at most one NOT. Prove size-preserving monotone replacement.

## repo_review — template and format review

Updated CONTRIBUTING requires helpers inside the file-owned namespace; final theorem uses its full name at top level and comes last. Guard command: `node .github/scripts/outside-guard.mjs imports <actual-file> <imports.json> lean/PEqualNP/Outside/L_meta_10760.lean`. Checker now supports check/refute/reduce.

L_meta_10758 is 6515 lines / 414104 bytes; it proves arbitrary-NOT lower bound 13 with a 13-gate monotone witness. L_meta_10762 is 3797 lines / 226340 bytes; it proves arbitrary-NOT lower bound 12 with a 12-gate monotone witness. Both final proofs ignore the one-NOT hypothesis. Engines adapted from L_meta_1673 (Trey Kind, PR 6929, Apache 2.0); preserve attribution when copying. Core recipe: truth-table bitmask circuit interpreter -> Sol -> minimized live-wire states -> finite-search no-solution certificate -> fixed monotone witness.

Graph-isomorphism scan: 891 L_meta files containing Fin 7; parsed final full-name edge-list theorem templates and checked all degree-preserving vertex permutations. None isomorphic to target. Same-degree candidates:
- lean/PEqualNP/Outside/L_meta_10758.lean
- lean/PEqualNP/Outside/L_meta_11425.lean
- lean/PEqualNP/Outside/L_meta_11944.lean
- lean/PEqualNP/Outside/L_meta_11968.lean
- lean/PEqualNP/Outside/L_meta_10618.lean
- lean/PEqualNP/Outside/L_meta_11413.lean
- lean/PEqualNP/Outside/L_meta_11381.lean
- lean/PEqualNP/Outside/L_meta_10624.lean

- 2026-11-25T19:21:16.757000+00:00: lower_bound agent independently scanned 891 seven-input proof files; 120 explicit 12-edge graph candidates; no target isomorphism. Target degree sequence [4,3,3,3,3,4,4]. Nearby 10762 proves unrestricted-NOT lower bound 12; 10758 lower bound 13. No generic one-NOT replacement theorem found in imported definitions.

Robust scan also searched every file containing `Fin 7`, parsed the entire final declaration (including multiline types), accepted `List Nat` or `List ℕ`: 1290 files, 120 twelve-edge candidates, 10 same-degree candidates, no isomorphism.

- 2026-11-25T19:23:01.743946+00:00: lower_bound strategy found reusable numeric targets for finite certificate regeneration by matching induced graph types to existing Imp [] Z L tables. Data: results/orch/lemmas/lower_bound_restrictions.json (each record gives candidate L and source file/Z). Candidate vertex-zero bounds: 10 for masks 1,2,4,8,16,32; 9 for mask64. Pair masks mostly7, masks12/68/72 give6. These must pass regenerated okE locally; no direct theorem transport assumed. Excluded transformed f/rp proof sources to avoid invalid source-mask correspondence.

- 2026-11-25T19:23:24.170753+00:00: graph_search: exhaustive quadratic-state formula DP over 8,771 states gives first formula at14 gates; biclique DP and shared-OR MILP independently give14. Explicit14-gate circuit checked on all128 inputs in Python; witness sent proof_template. These are upper bounds only for general circuits. Search artifacts /tmp/oec/pequalnp-pilot-182/graph-{search.py,milp.py,formula.cpp,formula.log}. Starting stochastic13-gate counterexample search with at mostoneNOT.

## Independent partial review (repo_review)

Named 36-line file reviewed: 14 binary AND/OR gates, references strictly earlier wires, output 20. Independent Python enumeration matches the exact posted edge function on all 128 assignments. Only import PEqualNP.Defs; helpers confined to own namespace; no forbidden strings/commands/options. Git status shows only new named proof file and results directory, no tracked-file edits. Approved for PARTIAL push once named lake build passes. This is not a proof of the complete statement: final theorem and 14-gate lower bound are absent, so final guard/checker acceptance must not be claimed. SHA256 fddf0763607e156a803cf41fca0eb4dda420ce81553054886a9ed9f59d8482e2.

- 2026-11-25T19:24:20.016282+00:00: graph_search: independently synthesized matching upper bounds for all one- and two-variable-zero restrictions. They exactly match lower_bound agent certified targets: singleton masks1/2/4/8/16/32=10,64=9; pairs=7 except12/68/72=6. Explicit formulas in /tmp/oec/pequalnp-pilot-182/restriction-upper-bounds.json.

## Toolchain setup 2026-11-25T19:24:21.471566+00:00

The supplied environment had no Lean or warm cache. Installed official Lean 4.36.0 in `/tmp/oec/pequalnp-pilot-182/lean-4.36.0-linux`; prepend its `bin` directory to PATH. Shallow-cloned all nine manifest dependency revisions. Ran targeted `lake exe cache get` on the 67 direct Mathlib imports under Defs; it exited 0 after downloading/decompressing 2480 artifacts. No Mathlib source compilation. Complete logs: `cache-get-2.stdout` and `cache-get-2.stderr` in task scratch. Removed redundant compressed artifacts using cache clean!.

- 2026-11-25T19:24:24.687690+00:00: graph_search independently synthesized matching formula upper bounds for all singleton/pair induced restrictions; candidate numeric lower bounds there are optimal. Lower-bound agent emitted RestrictionCandidates.lean in scratch, with all110 positive-bound records grouped by popcount. Target has 2 automorphisms.

repo_review: current upstream guard contains no general numeral-length limit, but join.txt states <=20 digits. proof_template KernelEngine splits large masks into <=16 hex digit chunks; independent scan found zero oversized literals. Guard detects only the expected missing final top-level theorem; no other format issue.

Independent shared-AND search completed all 12 target-edge seed gates. Treating each as a free reusable input in the 8771-state formula DP (then adding one gate for its construction) found no <=13-gate circuit; seeds 02,14,35 achieve14. This is an upper-bound search, not a general circuit lower-bound certificate.

## proof_template, 2026-11-25 19:27 UTC
- Selected L_meta_10762 finite unrestricted-NOT lower-bound engine (3,797-line source). Reconstructed its graph-specific truth samples exactly:64 positive assignments, all edge minterms against zero/endpoints/maximal independent sets, and true triples against false pair subsets; each pair duplicated in positive/negative grouped segments.
- Generated target501-column paired encoding with189 unique critical pairs. KernelEngine.lean scratch:3,568 lines,212,543 bytes, named sections and ≤16-digit hex chunks. Independent guard review finds only missing top-level final theorem (expected for prefix).
- Extracted88 pure computation definitions to Std-only NativeEngine, replacing recursors with match wrappers and Bool.rec with lazy bif; search tool compiles. Original kernel definitions remain authoritative in final proof.
- Native okE checks established all110 candidate proper induced-subgraph bounds in about2seconds. Full root14 search running by NOT count; t0 on proof_template, t1+ on lower_bound.
- Named final partial file has14-gate circuit correctness/equivalence/monotone/length helpers (36lines); root compiling and checkpointing it.

Independent mixed-restriction validation: all 49 OneRestrictionCandidates entries checked over all128 assignments. Residual function exactly OR(singleton neighbors) plus disjoint residual edge/triangle. Candidate numeric bounds equal explicit monotone formula upper bounds: one1at0/5/6 ->5, one1at1/2/3/4 ->7; mixedneighbor0 reducesone; mixednonneighbor0 yields3 or4. Lower-bound truth still requires certificate engine; no overlarge candidate against these constructions. Full data scratch review-mixed-restrictions.json.

- 2026-11-25T19:28:09.246279+00:00: graph_search: bundled CaDiCaL located. Three bounded300s13gate SAT searches active: custom all128rows oneNOT, custom canonical-topology variant, official LinkN2 arbitraryNOT boundary-row encoding with textual LRAT output. Forced known14gate witness validates custom encoding (SAT). The official route has generator notes/data/lrat-link/genrow.py --not, potentially useful if UNSAT.

- 2026-11-25T19:28:49.028928+00:00: root prioritizes successful native lower-bound route. Stopped stochastic13gate and both custom SAT jobs; best stochastic circuit had1error, no exact counterexample. Official LinkN2 SAT/LRAT job remains bounded300s, niceness19. All codes/fulllogs retained in scratch.

## Checker environment 2026-11-25T19:29:11.929098+00:00

`tools/check-lean.mjs` uses the repo queue shim, which selects `PEQUALNP_REAL_LAKE` or an elan proxy rather than PATH. Set `PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-182/lean-4.36.0-linux/bin/lake` and `PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-182/pnp-home`; include toolchain bin on PATH. The checker strips inherited LEAN_/LAKE_ options but keeps PEQUALNP_* configuration. Each stage timeout is 30 minutes with 64MiB captured output. `.lake/check.lock` serializes checker runs. Prebuilding `checklemma` at nice priority 10.

Verifier prebuild completed successfully at 2026-11-25 19:29:52 UTC. Complete logs: scratch `checklemma-build.stdout` and `.stderr`; five build jobs, CheckLemma 10s, native object 8s, executable 15s. Disk free approximately 498MB. No full checker invocation yet.

## Independent compiled-engine checkpoint review (repo_review)

KernelEngine SHA256 8893ec316db35760aff6cab0b50a420ee649e6cb0c396374e80863788ebf7923; 3569 lines / 212543 bytes. Compared complete declarations against L_meta_10762: no added declaration names; generic lemma/theorem proof changes only namespace10762->10760 and names on section closures. Modified definitions are graph constants/masks and section boundaries; removed declarations are old graph certificates, bridge, circuit witness and final theorem. No new axiom/sorry/native/unsafe/opaque/compile-time construct; only allowed PEqualNP.Defs import. Guard reports exactly missing full-name final theorem, as expected. APPROVED for partial artifact preservation push after reported successful compile; not approved as complete proof or accepted checker result. Full diff saved in scratch review-engine-full.diff.

- 2026-11-25T19:30:40.824366+00:00: graph_search: stopped officialSAT to conserve disk for main Lean route; no SAT/UNSAT verdict. Complete unfinished LRAT stream losslessly gzip-compressed after SHA256 roundtrip verification, original188305408bytes, compressed54071135bytes. Fullstdout/stderr retained.
