# Library route review for L-meta-10760

Checked 2026-11-25 after upstream refresh to 3e44154b.

## Semantics

`PEqualNP.Defs.CircuitLowerBounds` has definitions only; imports through allowed `PEqualNP.Defs` expose Gate/GateOp/Circuit and MetaComplexity.HasCircuitSize/FanInTwo. Gate evaluation is a left fold adding one wire per gate. Future/out-of-range wires read false. Empty AND and empty NOT give true; empty OR false. NOT ignores all but its first input. Any normalization must cover these semantics.

## Reusable source engines

Other Outside imports are forbidden for our gap. These proofs are reusable by copying needed declarations into our own helper namespace, with attribution if comments retained.

- `L_meta_10762.lean`: 3797 lines, only imports PEqualNP.Defs. Generic truth-word live-frontier engine and recursive Boolean exhaustive search, with graph-specific packed positive/negative sample rows. Proves unrestricted AND/OR/NOT lower bound 12; final witness is monotone size12, so one-NOT premise is unused.
- `L_meta_10758.lean`: 6515 lines, enhanced version of the same engine. More pruning machinery and certificate chunks.
- `L_meta_10756.lean`: 4720 lines, imports Mathlib and PEqualNP.Defs. Generic DAG certificate engine through approximately line3738. Main12 lower-bound certificate uses513 states, supported by52 lower-bound restriction records. Exact child-state recurrence is simple enough to port to Python/C++.
- `L_meta_10750.lean`: related lowerDag/BinEngine extended engine; source credits L_meta_8503.

No graph isomorphism exists between our graph and any posted graph in existing files matching L_meta_106*, L_meta_107*, or L_meta_108*. Only10758,10618,10624 share the degree multiset [3,3,3,3,4,4,4]. Checked all5040 permutations subject to degree preservation for those three.

## Alternate DAG search algorithm (10756)

State = (remaining gates, sorted distinct live truth-table words, generated-gate history). Initial live set is a subset of input truth words; essential-input witnesses can rule out all proper subsets. For each state, choose AND or OR of every distinct pair, or NOT of each live word. Binary transitions independently retain/drop each operand (4 choices), unary transitions retain/drop operand (2). Drop constant, duplicate, and invalid outputs; otherwise insert output, decrement remaining fuel, prepend history triple. This is complete by the proved LiveWord normalization.

Pruning includes:
- live count > remaining+1;
- positive/negative truth rows no longer distinguishable by live words;
- tight live count = remaining+1 forces zero remaining NOTs and a Karchmer-Wigderson rectangle partition;
- previously established restriction lower bounds, with replay of history to bound reconstruction overhead.

The generator emits forest parent/token entries for reachable non-pruned states; links identify each child with a state (possibly through input automorphism). `lowerDag` at3258 checks every root, node, child link, and restriction premise. The root certificate gives `Lower mask stock goal (fuel+1)`. Circuit bridging at the end transfers this to arbitrary Gate lists.

## 10762 packed rows (handed to certificate_search agent)

NN=500. First64 columns are positive assignments sampled from full truth table. AA marks378 comparison bits, representing189 unique positive/negative pairs twice. `segsX` groups bits with identical positive row; `segsY` groups bits with identical negative row. For its graph there are41 distinct positive rows (edges and selected triples),17 negative rows (all independent assignments, alpha2). For edge mask5, negative comparisons are maximal independent sets [3,6,9,12,18,24,48,72,96] plus its false subsets [0,1,4]. Positive triple7 compares to3 and6. This explains data generation; certificate_search agent owns generation now.

## Final format reminder

All copied helpers belong inside namespace PEqualNP.Outside.L_meta_10760 (or its _aux namespace), with named end at column0. Final target theorem fully named, last, outside helper namespace. Run current outside-guard with actual path, imports JSON, repo-relative path, and kind check. Do not import any source Outside engine.

## Independent review of first partial

Verdict: PASS FOR PARTIAL PRESERVATION, pending Lean build; not a complete proof or PR.

Reviewed named Lean file SHA256: ca6b8436dc09c0aa2e332340a368d55c0dda2e13752a920d237e1864eca26bdb.

Independent evaluation verified all128 input assignments, fourteen binary AND/OR gates, backward-only wire indices, output20, graph edge list equal to desk statement, and graph_correct right-hand side verbatim contained in posted statement. No prohibited proof constructs found. Helper namespace and scoped limit options follow current format. Only named Lean file plus authorized intermediate notes are untracked; no existing tracked files modified.

The full target theorem is intentionally absent. Full checker/format guard cannot yet accept a completed contribution. Root must record the Lean build before push-early preservation.

## SAT/LRAT fallback feasibility

The pinned toolchain has a sound direct LRAT checker (`Std.Tactic.BVDecide.LRAT.check_sound`), but the ordinary `bv_decide` and `bv_check` frontends call `nativeEqTrue` unconditionally in `Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:40`; there is no kernel-only flag at that call. They also fail the plain-file rule. Mathlib `from_lrat`/`lrat_proof` generates kernel proof terms but consumes strings and does not fit the requested file format.

A better existing implementation is `lean/PEqualNP/Library/LRAT/Checker.lean` (578 lines). It provides kernel-only RUP checking with `check_sound`, packed `checkW_sound`, and bounded-memory segments `checkFirst_sound`, `checkSeg_sound`, `checkLast_sound`. It is designed for `decide +kernel`, using a binary trie and Nat bitsets/raw recursion. Copy it into our helper namespace rather than importing its disallowed project module.

`Library/LRAT/LinkN.lean` (1277 lines) already handles arbitrary AND/OR/NOT fan-in-two Gate lists, including malformed/future wire defaults and empty gates, and proves `link` plus `lower_of_unsat`. `LinkN2.lean` adds lexicographic ordering of independent gates. Unlike the monotone-only root definitions `Defs.LratEncoding`, these local definitions include NOT. Copy needed sources and basic Shannon wire-fold lemmas; inline the local `wdt` tactic macro (LinkN:290 and LinkN2:524), because new macros are forbidden. For an unrestricted circuit lower bound, no one-NOT counting lemma is needed. A one-NOT-specific CNF would additionally require proving that normalization preserves the NOT budget.

Bundled solver `/tmp/oec/pequalnp-pilot-178/toolchain/lean-4.36.0-linux/bin/cadical` supports `--lrat --no-binary input.cnf proof.lrat` according to its checked help. The custom project checker accepts RUP only; check generated certificate for RAT/negative hint indices before conversion. Tokens per derived clause are its new store key, encoded literals,0, then hint-key/unit-literal pairs ending at a conflicting hint key. The explicit units can be generated by replaying LRAT hints outside Lean; the checker proves they are correct. Large constants must be split to comply with numeral-length and512KiB file limits.

This establishes a feasible alternate architecture, not a generated certificate or compiled proof of our gap.

## Kernel SAT fallback assembly (2026-11-25)

Prepared `/tmp/oec/pequalnp-pilot-178/lrat_route/Engine.lean` (2,265 lines, about97KB): kernel LRAT checker, minimal Shannon wire lemmas, LinkN and LinkN2 exact synthesis encoding and soundness, all under the permitted gap namespace and importing only PEqualNP.Defs. Local tactic macros are inlined. Exposes `lower_of_certificate` and `lower_of_packed_certificate`, deriving `s+1 ≤ C.size` for unrestricted fan-in-two circuits from checked UNSAT tokens. Not yet compiled: root prioritized Lower13 after the initial target build.

Independently reviewed finite_search's `linkn_enc2.py`: clause families and ordering match LinkN.enc plus LinkN2.fLex. Full128-row13-gate formula has107,942 clauses and16,501 DIMACS variables. Its first solver run stopped without verdict after115.49s and generated121MB LRAT.

Prepared untrusted `lrat_route/convert_rup.py`: backward slicing from the empty clause, dense clause renumbering, RUP replay, and packed token JSON. It rejects negative/RAT hints and still requires kernel checking.

At19:12UTC the LRAT assembly compiled successfully with exit0, importing only PEqualNP.Defs. Exact file2,261lines/97,228bytes, SHA256 `c4151f1ff635044398889e5481d8fb484f6e0afb7e46ec15c74e39270972d9f9`; complete37,407-byte log `lrat_route/engine-build.log` has zero errors and inherited linter/deprecation warnings. Both generic bridge theorems and the toy `decide +kernel` checker invocation were accepted. Current one-NOT extraction route is primary; SAT was not restarted.
