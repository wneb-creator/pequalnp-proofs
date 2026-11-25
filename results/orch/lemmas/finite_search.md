Finite search strategy — L-meta-10760

At 19:02 UTC, exact weighted biclique cover DP gives a 14-gate monotone formula:

x6 & (x0 | x2 | x3 | x5)
  | x3 & (x1 | x5)
  | (x0 | x1) & (x4 | x5)
  | x2 & (x0 | x4).

The 66 possible nonempty disjoint bicliques cover the twelve edges. The DP minimizes sum(|A|+|B|)-1 and returns 14. This is only an upper bound on circuit complexity, since absorption and sharing can improve formulas.

A repository-wide scan of the 997 final statements using the one-NOT hypothesis found no isomorphic seven-variable graph. The ten same-degree candidates were 10624, 11413, 11968, 11425, 11066, 11944, 10758, 11381, 11419, 10618.

No Python z3/pysat/ortools module or SAT executable is installed, but /usr/lib/x86_64-linux-gnu/libz3.so.4 exists. A ctypes SMT-LIB wrapper performs synthesis without any install or network access. Scripts and complete solver output are under /tmp/oec/pequalnp-pilot-178/finite_search/. Monotone synthesis checks the twelve minimal positive assignments and maximal independent negative assignments, which is complete for monotone circuits. One-NOT search checks all 128 assignments. Search outcomes pending.

The nearby 10762 proof gives a 12-gate all-NOT lower bound through a verified live-wire and packed-bit search. Its row constants are graph-specific; certificate_search owns regeneration. Of the 500 bit positions, 378 active AA bits represent 189 positive/negative assignment pairs repeated twice, once grouped by each endpoint. First 64 fingerprint rows are other positive assignments.

At 19:07 UTC: the MILP allowing all OR-subset DAG sharing and biclique-product covers reported optimum 14 within that circuit class (computational evidence, not a Lean proof) (29 wall seconds). Thus a 13-gate monotone circuit, if one exists, must use more general nesting/absorption.

Initial SMT and CaDiCaL runs at 13/14 monotone gates timed out; no SAT or UNSAT verdict was obtained. Full logs retained. Native solver process CPU was only about 30 seconds during each 120-second wall timeout, indicating heavy shared CPU contention. All solvers stopped at root request to prioritize the initial Lean build.

A Python exact translation of LinkN.enc ++ LinkN2.fLex lives in finite_search/linkn_enc2.py. It preserves clause family order and uses the natural-to-DIMACS literal conversion. Independent reviewer found no mismatch. For n=7,s=13 and all 128 rows, it emits 107942 clauses, variable maximum 16501. The LRAT-generating search can restart after the initial build completes; no verdict yet.

At 19:33 UTC, the checked-proof resource task replaced SAT work. Instrumenting the Python engine at its first continuation boundary produced:

- Unary first: 54 distinct `look(13,11,0,z,v,0)` states; every result false. Independent recursive costs range from 112 to 519 states, summing to 12,642 with a fresh cache per child.
- Binary first: 42 distinct `look(13,12,1,z,v,1)` states; every result false. Costs range from 2,885 to 32,450, summing to 647,198 with fresh caches. Many binary pieces still need finer subdivision.
- Both roots have exactly one accepted initial wire subset.
- `children-packed.json` (132 KB) interns 104 W records; every record has initial-input, NOT, AND, or OR parent provenance. State lists refer to W-table indices.

Artifacts: `finite_search/unary-children.json`, `binary-children.json`, `children-packed.json`, and their trace scripts/logs under the task scratch directory. Reviewer and certificate_search have the paths. No SAT workers remain active.

At 19:38 UTC, an additional one-step split of all 42 binary children completed:

- 3,199 unique continuation states, all false in Python.
- Largest subtree: 4,061 calls; 135 states exceed 1,000; total fresh-cache calls: 556,417.
- State shapes: `(fuel,k,t,mode) = (12,11,1,1), (13,10,0,0), (13,11,1,0)`.
- 1,984 distinct z budgets. 763 W records including intermediate parents; every W has initial/NOT/AND/OR provenance, found within three layers.
- Compact source estimate: W provenance 11.8 KB, z limbs 140.9 KB, states 97.1 KB. Removing the fixed high bit from each five-bit z counter should save about 30 KB before decoder overhead.
- Artifacts: `binary-depth2.json`, `binary-depth2-packed.json`, `split_binary.py`, `pack_depth2.py`, complete logs in task scratch.

Simple modulo hashing of child state values was poorly balanced and needed many buckets; explicit packed states currently offer a more predictable route. No worker remains running.

Shared data and batching update:

- `BinaryDataCompact.lean` is an immutable, uncompiled fragment of 236,538 bytes with indexed `binW`, `binZ`, `binRow`, `binMode`, `rootRow`, `parentFIndices`, `parentGIndices`, and `unaryRow`. It merges all unary records into the same pool. Original binary leaf IDs remain unchanged.
- Lower13 t0 has 21 immediate children, all false, max 2,270 calls. Optional fallback splits only children above 1,500 calls: 261 leaves, max 1,335. Both packed reports remain available.
- Every lower0 child i exactly matches `rootRow (2*i+1)` after changing k/t to 11/0 and subtracting `initG / 16` from z. `Lower0SharedData.lean` replaces duplicated data with this tiny accessor.
- Full descendant-set profiling found 311,741 unique states across the binary leaves, versus 556,417 when each leaf is checked separately.
- Greedy overlap batches: cap 3,000 gives 162 groups / 489,561 estimated states; cap 4,000 gives 119 / 472,635; cap 6,000 gives 76 / 455,458; cap 8,000 gives 56 / 441,922.
- Representative cap-6,000 group 5 and cap-8,000 group 0 were evaluated directly with persistent Python caches; actual call counts were exactly 6,000 and 8,000 respectively, matching estimates, with all results false. Certificate_search is benchmarking their Lean memory use.
- Lower0 grouping at cap 3,000 gives 11 groups / 29,668 states, only about 9% lower than separate checks.

All group tables partition the binary leaf IDs exactly. Descendant hashes are used only for performance estimates and grouping; no mathematical validity depends on them. No worker remains running.

Coverage hashing and final size:

- `BinaryDataHashedMin.lean` is the preferred immutable data fragment: 231,739 bytes. It keeps indexed binary/root/unary rows, removes parent-specific F/G maps, and supplies global budget buckets.
- Binary bucket modulus is 2053, with at most 10 candidate rows. Mode-filtered accessors are `binFCandidates` and `binGCandidates`. Root, unary, and lower0 bucket modulus is 127, with maxima 2, 4, and 1. Full tuple equality is still required after bucket lookup; hashing is only an accelerator.
- Modulus 2048 was rejected because packed z budgets concentrate in only 18 buckets, with up to 517 entries.
- `BinaryDataHashed.lean` is the same fragment with normal comma spacing; `BinaryDataHashedMin.lean` saves 8,620 bytes solely by removing spaces after commas.
- Leaf benchmark batches were sent to certificate_search: cap 6,000, group 5 has 6,000 union / 8,442 fresh states; cap 8,000, group 0 has 8,000 union / 12,326 fresh states. Both were independently replayed in Python with matching exact call counts and all false results.

Kernel lookup optimization:

Pinned Lean source confirms that arrays are list wrappers for proof reduction (`Init/Prelude.lean`, Array declaration around line 3350). `Array.getD` computes a bounds check using list length and then list indexing. Thus a flat 6,114-element budget-limb table is expensive inside kernel checks.

`CertificateDataChunked.leanfrag` is an isolated variant of the latest canonical spread-decoder/noncomputable data. It splits every table larger than 64 entries into 64-entry chunks, preserves every original entry and ID, and retains all row interfaces. Its size is 230,522 bytes. Fast bucket accessor names are `binBudgetAt`, `rootBudgetAt`, `unaryBudgetAt`, and `low0BudgetAt`; nested table names end in `BudgetBucketChunks`.

`CertificateDataChunkedList.leanfrag` differs by one helper implementation: each lookup uses `Array.toList.getD` at both levels, avoiding Array's separate length checks. Pinned `Init/GetElem.lean` confirms list lookup recurses directly to the requested index. Both variants are uncompiled by finite_search; certificate_search owns benchmark slots and reviewer owns bound-proof adaptation.

### 2026-11-25 resource profiling: chunked batches

Pinned Lean Array kernel implementation wraps a List; Array.getD computes a length bound and then indexed list access. Chunking the large constant tables into 64-entry arrays allowed the 6k-state benchmark to pass at 5.38GiB, where the flat tables exceeded 6GiB. Isolated variants `CertificateDataChunked.leanfrag` and `CertificateDataChunkedList.leanfrag` preserve every ID; the latter uses List.getD on chunk lists to avoid redundant length scans. Hash bucket modulus remains 2053 (not 2048, which clusters the packed budgets badly).

Every 6k grouping replayed False in Python with an independent fresh cache per group: 76 groups, 455458 distinct state evaluations, 23.661 CPU seconds total. Benchmark group5 is ordinary work: 18 initial rows, 6000 unique states, 8442 fresh-state sum, 27 distinct initial W records, 0.294 CPU seconds vs median group 0.309. Worst single leaf2555 requires 4061 states and 0.156 CPU seconds. Thus group5 costs 1.89 times that control in Python but 4.39 times in current kernel measurements (37.7 vs 8.59 seconds); the slowdown cannot be explained just by arithmetic workload. Strict initial-value forcing is being tested by certificate_search.

Useful representative groups for Lean benchmarks are group0 (9 rows, 6000 states, 0.277 CPU seconds), group55 (104 rows, 6000 states, 0.466 CPU seconds, slowest Python group), and group75 (393 rows, 5458 states, 0.258 CPU seconds, stresses decoding many initial rows). Full measurements are in scratch `group-timings-6000.json`; all mathematical leaf results remain checked by Lean separately.
