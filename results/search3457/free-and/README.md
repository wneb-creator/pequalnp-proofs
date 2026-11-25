# Auxiliary free-AND OR-count search

This is an auxiliary search for an OR-count lower bound, not a Lean proof and not a result establishing L-meta-3457.

For N4 incidence mask13726, allow at most seven binary OR gates with unlimited free AND operations. Each OR operand and the output is an arbitrary conjunction of input variables, an explicit false constant and previous OR outputs; the empty conjunction is true. Both constants are free. All singleton restrictions on internal AND gates are omitted, enlarging the circuit class. Missing OR gates can be padded by false OR false. Collapsing AND-only regions of a circuit therefore yields this model without increasing OR count. These translation claims were independently reviewed but are not Lean-certified.

The critical-row CNF has2030 variables and8758 clauses over26 assignments: every edge pair, every maximal independent set and every singleton. Exact Tseitin clauses encode selector-and-negated-source products, De Morgan turns selected ORs into selected ANDs, and every counted OR is exact. Monotonicity makes the positive edge pairs and negative maximal independent sets sufficient for full-function correctness. A SAT witness would additionally be scalar-checked on every one of256 assignments.

The authorized run returned UNKNOWN after120.104 seconds (exit0). It establishes no OR-count lower bound and supplies no circuit witness. All stdout/stderr, wrapper logs, solution status, result JSON, CNF and mapping are preserved. No proof certificate was requested. Solver cap256MiB, internal limit120 seconds, external wall limit125 seconds, default seed0, pinned CaDiCaL2.1.2.

```sh
python3 results/search3457/free-and/free_and_or_sat.py --N 4 --mask 13726 --ors 7 --seconds 120 --solve --outdir results/search3457/free-and
```

The counterexample_search agent independently reviewed the encoder before the run; lower_bound authored it. A subsequent optional pruning idea is to require every flattened AND region selecting at least two distinct leaves to be singleton-zero. This is necessary for a singleton-clean original circuit, but weaker than requiring a clean binary expansion. That follow-up was not part of this recorded unrestricted run.
