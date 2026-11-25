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
