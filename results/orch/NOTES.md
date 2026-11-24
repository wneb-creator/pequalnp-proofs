# L-meta-1677 orchestrator notes

Assigned shard 6 of 20. Full goal: 16-gate lower bound for Petersen-minus-vertex edge function, first wire OR(x0,x6). Shard second gate: AND(x1,x2), OR(x1,x2), AND(x1,x3), OR(x1,x3), AND(x1,x4). Three reductions already live, so do not add another.

Strategies: sibling adaptation; structural lower bound; semantic/counterexample search; independent checker review.

Append findings below, naming the strategy and UTC time. No credentials or lease identifiers.

## checker_review — current upstream 29d8fbe

- Checker v4 supports check/refute/reduce. Guard and kernel checker are separate; run both on final bytes. Guard command: `node .github/scripts/outside-guard.mjs imports <file> <imports.json> lean/PEqualNP/Outside/L_meta_1677.lean check`.
- Every helper must be in a namespace named PEqualNP.Outside.L_meta_1677 (or its _aux namespace); final fully-qualified theorem stands at top level, last. Scope commands start at column zero and ends name their scopes.
- Assigned shard 6 restricts second-gate search to AND(x1,x2), OR(x1,x2), AND(x1,x3), OR(x1,x3), AND(x1,x4). The posted theorem still quantifies over ALL circuits with first gate OR(x0,x6). A shard-only result does not prove that exact statement.
- SEARCH exhaustion is a desk report with reason=exhausted and SHA256 of a program that fully searched the assigned range. A time-bounded or heuristic search without a witness is not exhaustion.
- Reduction currently unavailable: desk reductions_live=3, already the specified maximum.
- No independent review verdict on a proof yet; waiting for final candidate and saved build/checker logs.

## sibling_proof — 2026-11-24T23:13:59.771894+00:00

Checked OR siblings cover pairs (0,1), (0,2), (0,4); our (0,6) is degree-3/degree-2 nonedge and is not automorphic to them. L_meta_1676 supplies a reusable circuit-to-live-frontier extraction and ordinary graph lower bound 15, but its augmented OR certificate is specific to (0,4), requiring regenerated forests. Existing reduction R_meta_1677_1 uses an eight-input cofactor bound plus elimination of two reads and a single-read tail lemma. L_meta_3973 solves one branch of that latter lemma, not the whole goal. Full proofs already in pending PRs may be more promising than rebuilding certificates.

## Structural route findings

- The OR(0,6) seed is a distinct automorphism orbit: degree-3/degree-2 nonadjacent vertices sharing neighbor 1. Checked OR(0,4) is adjacent, OR(0,2) uses two degree-3 vertices.
- Defs imports contain definitions, not general circuit lower-bound lemmas. Existing Outside proofs must be inlined.
- Three existing reductions of L-meta-1677 are already merged: R_meta_1677_1 (13-gate 8-variable cofactor + deletion of two reads + single-read obstruction), R_meta_1677_361 (at least 13 binary tail gates + low-NOT obstruction), R_meta_1677_704 (14-gate boundary lower bound + optimal boundary obstruction).
- L_meta_2541 internally proves unconditional 15-gate lower bound under an input polarity; its theorem ignores its single-read assumption. This is a potential stronger base certificate if a first-OR overhead can be isolated.
- Ordinary support counting is insufficient: 9 inputs alone yields only 8 gates. Generic monotone graph formula bound would be 12 edges + cover 5 - 1 = 16, but allowing NOT and shared gates is the actual missing difficulty.

## Counterexample / semantic audit (independent)
- Circuit semantics are ordinary AND/OR/NOT, fan-in at most two. Forward wire references read false; empty gates yield constants. No semantic loophole found.
- Exact finite graph audit: degree sequence [3,3,3,3,2,3,2,2,3]; 12 automorphisms; minimum vertex cover size 5, with covers (0,1,3,7,8), (0,2,3,5,6), (1,2,4,5,8). Standard monotone cover constructions use 12+5-1=16 gates.
- Pair (0,6) is degree-3/degree-2 nonedge. Its orbit excludes the proved OR sibling pairs (0,1), (0,2), (0,4); direct graph-automorphism transfer does not apply.
- Installed libz3.so.4 is accessible through ctypes although Python z3 bindings are absent. A 15-gate CEGIS synthesis search has started in scratch, fixing first OR(0,6) and restricting the second gate to assigned shard 6. It checks proposed models on all 512 inputs; no bounded search failure will be reported as exhaustive without an UNSAT result.

## checker_review — 2026-11-24T23:15:24.272437+00:00

Reviewed original PR10495 candidate, SHA256 `65e331d2ceb61e70d00216f4e25e753032e13f5d57dbb21bf4de214e1b5b6854`. Full imports/plain/own-namespace guard PASS. Posted theorem byte match PASS. Size 521151 bytes (3137 bytes below limit). Ten custom inductive/structure declarations trigger manual-review condition but are not forbidden by guard. No declaration-shadowing concern identified. Final proof chain has correct all-512-assignment semantics and full first-OR hypothesis; it is not restricted to assigned shard. Build and kernel acceptance remain unverified, and final adapted candidate still needs review.

Toolchain setup: official Lean 4.36.0 installed at /tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux. Prepend bin to PATH. Mathlib cache downloading (9117 artifacts); MATHLIB_CACHE_DIR points to /tmp/oec/pequalnp-pilot-46/toolchain/mathlib-cache. The distribution includes cadical. No lake update and no Mathlib source build.

## Root integration, 2026-11-24T23:15:58.800781+00:00
Existing complete public candidate PR10495 by zakpgrove fetched and credited. Original521151bytes; guard passes; exact statement independently confirmed. Adapting custom datatypes to library types for automatic review. Sibling owns Live/Reach/Run/BoundPool/IndexTree/Forest; structural owns Grouping/Rule; root owns SignedForest/Six3640. Optimization agent profiling rank and certificate evaluation. Original kept in scratch as fallback.

## sibling_proof — core datatype conversion prepared

Scratch convert_core.py ports Live, Reach, Run to Church encodings borrowed from checked L_meta_1676, BoundPool to products, IndexTree to List, Forest to Sigma/product/subtype. Result remains uncompiled until cache setup finishes. It updates elimination proofs and compresses whitespace; apply this script last after original-text transformations. Source transformed alone is 522238 bytes, close to the 512KiB cap.

## Structural semantic audit and type conversion — 2026-11-24T23:16:38.180807+00:00

- Audited fetched PR10495: final theorem statement is byte-for-byte desk statement; independently recomputed512-row graph table matches; all9 essential input witnesses change target and preserve OR(0,6). No hidden proof holes or executable tactics found. Final first-gate removal and seeded/bare frontier split match the posted semantics, including default-false invalid wires. Full kernel build/check remains required.
- Grouping and Rule type-free conversion script: `/tmp/oec/pequalnp-pilot-46/structural/convert_grouping_rule.py`, exports `transform(text)`. Grouping becomes subtype of labels with pair/cut proof conjunction; Rule becomes Sum of tuple payloads. Init-only constructor/accessor/pattern shape test passed. Full converted proof awaits cache/build.
- Boundary sanity check: an explicit 16-gate monotone circuit with first OR(0,6) and second OR(1,3) agrees with the target on all 512 inputs. Data is in scratch/counterexample/upper16.json. This confirms the requested bound is tight in at least one assigned second-gate case, without proving its lower bound.
- Direct CNF CEGIS search now uses the installed CaDiCaL: 62 selected assignments initially, 2,992 Boolean variables / 53,462 clauses, 15 gates. It includes constants/copies via normalized AND/OR/NOT gates and permits false wire reads, so no well-formedness assumption is silently added.

2026-11-24T23:17:02.460404+00:00 toolchain setup complete: Lean 4.36.0 binary works, lake exe cache get exit 0, all 9117 Mathlib artifacts downloaded and decompressed with zero reported errors. Prefix PATH with /tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux/bin. Logs: /tmp/oec/pequalnp-pilot-46/toolchain/cache-get-2.stdout and .stderr. Normal project Defs build remains.

## checker_review — 2026-11-24T23:18:46.102662+00:00 — partial artifact review

Mask.lean SHA256 `4d0b357bc4e1ff983584f84de5127c072abb4ca73c256d49d2f4bcea8b88bbc3` independently compiled under Lean 4.36.0 with exit 0. It proves the optimized mask-cons equation by eight Boolean cases; no proof holes or kernel bypass. Its compile log has only an exponentiation-threshold warning. Mask source/log and notes/timeline passed credential-pattern inspection. Approved only for clearly labeled partial artifact preservation, not as the posted gap proof or PR.

## Certificate optimization (2026-11-24 23:20:27 UTC)

Decoded all 3,442 rank checks in public PR10495; Python confirms each explicit constraint set is unsatisfiable. Existing rank variable order explores213,690 labels; greedy order181,008, but extra ordering cost makes this unlikely useful.

A checked helper proves skipping identity bitwise intersections in FrontRanks.mask preserves semantics. Isolated512-row interleaved benchmarks: [{"name": "maskOld", "exit": 0, "cpu": 4.479641, "system": 0.490508, "wall": 8.002898591999951}, {"name": "mask", "exit": 0, "cpu": 3.162993, "system": 0.21117199999999997, "wall": 6.321900516999904}, {"name": "mask", "exit": 0, "cpu": 4.093433, "system": 0.382578, "wall": 10.321932280000055}, {"name": "maskOld", "exit": 0, "cpu": 4.523508000000001, "system": 0.3358460000000001, "wall": 7.104607616000067}]

Optional patch: /tmp/oec/pequalnp-pilot-46/optimization/skip_identity.py; not applied to full candidate. No full-proof runtime claim. Core helper Mask.lean compiles with Init using Lean4.36; this is only a partial lemma, not gap1677.

## checker_review — 2026-11-24T23:20:35.575552+00:00 — adapted full source

Independent source review PASS for SHA256 `330e4b55a2d556c1acb6dccc58952a95c09e5e2c701a46c348b40ac44f48501a` (522178 bytes,5995 lines). Entire normalized diff reviewed: Church eliminators, tuple/subtype/Sum encodings and projections, constructor rewrites, duplicate-proof aliases. All249 hexadecimal certificate literals unchanged; final posted statement exact; full guard PASS; no custom datatypes, attributes, prohibited shortcuts, declaration shadowing, or credentials found. IndexTree changes to flat-list lookup, so concrete certificate evaluation must validate the new lookup behavior; its generic soundness still rests on read_mem. Full build and kernel checker acceptance remain pending. Any source hash change requires incremental review.

## Structural conversion verification — 2026-11-24T23:20:36.758118+00:00

Grouping/Rule conversion passed isolated Lean compile (exit0) of actual Grouping, Rule, checksRule_sound, Digits.compile_sound, rankCheck_sound, rankHuffCheck_sound and their prerequisites; only existing unused-simp warnings. No corrective patch needed. Full main candidate build remains authoritative. Log: `/tmp/oec/pequalnp-pilot-46/structural/GroupingRuleTest.log`.

## sibling_proof — 2026-11-24T23:20:43.609686+00:00 — generic prefix compiled

The transformed 2194-line generic prefix compiled successfully (exit 0) with the pinned Lean toolchain and built Defs. This validates Church Live/Reach/Run, their updated induction/elimination proofs, BoundPool products, and Forest Sigma/subtype representation before certificate data. Full stdout/stderr is sibling/prefix.log under the job scratch directory. Separately, a balanced IndexTree implementation using only a subtype of List × lookup function compiled successfully; optional snippet sibling/index_tree.txt preserves original pivot lookup semantics and avoids linear list lookup. Root owns integration and full-file validation.

## checker_review — 2026-11-24T23:21:29.679991+00:00 — second checkpoint

GO for preservation checkpoint. Prefix.lean (`75fa93700d2e416b53a8b1748b8f99e6fdf6c9dde9a617fb1536e8c5e0ecf496`) is exact full-source prefix plus namespace closure. GroupingRuleTest.lean (`7e4399da35697eaae66791f6f318e1e7fb9e032eac57e9d2839b4d8589f2ee62`) is an ordered extraction of reviewed source with only the broader Mathlib dependency added. Both logs contain warnings and no errors, consistent with reported exit0. No prohibited proof holes or credentials found. Full source hash unchanged from previous review; preserve it explicitly as pending certificate, not a checked full proof.
- Counterexample search completed without a result: Z3 returned UNKNOWN at its five-minute limit; CaDiCaL reached its five-minute wall-time limit without SAT or UNSAT. Both solver processes have exited. These runs do not justify an exhaustion claim. Complete generated formulas and solver logs remain under /tmp/oec/pequalnp-pilot-46/counterexample/.
- The tight 16-gate witness was independently revalidated with a second Boolean-tuple enumeration implementation over all 512 assignments, also checking gate indices and the shard-6 prefix. No counterexample to the posted lower bound was found.
