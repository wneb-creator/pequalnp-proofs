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
