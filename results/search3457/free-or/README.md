# Auxiliary free-OR AND-count search

This tests an auxiliary AND-count conjecture, not L-meta-3457's total-size normalization. No Lean certificate has been generated, and no proof or refutation of the posted statement is claimed.

For N4 incidence mask13726 (the nine-edge theta graph), allow arbitrary OR subsets at each AND operand and at the output, with at most three binary ANDs. Require each AND false on every singleton input, and require the output to compute the graph edge function. No symmetry, dead-gate or edge-usefulness restrictions are imposed. Missing ANDs may be padded by false AND false, so the encoding includes all smaller AND counts.

CaDiCaL returned UNSAT in0.068 seconds, with exit20 and an UNSAT solution-status file. The CNF has559 variables and1780 clauses over26 critical rows. This verdict is about the saved CNF; the translation is independently reviewed but not formally verified. A proof certificate was not requested.

Each arbitrary-OR operand is encoded using Boolean selectors for all inputs and previous AND outputs. Exact Tseitin conjunctions encode selector-and-wire products; exact OR clauses combine them. AND truth values are exact conjunctions. Critical rows include all edge pairs, all maximal independent sets, and all singleton inputs. Because the generated circuits are monotone, accepting all edge pairs and rejecting all maximal independent sets determines the full edge function. A SAT result would also be independently scalar-checked over all256 assignments and all AND/singleton pairs.

Collapsing OR-only regions gives this model from any binary AND/OR circuit. Constants and copies can first be simplified without increasing AND count for the nonconstant target. False constants remain available as empty OR subsets. The singleton-clean condition is preserved on retained ANDs. This is an informal completeness argument, not a Lean theorem.

The counterexample_search agent independently reviewed the code before the root-authorized run; lower_bound authored it. After another fresh renewal, root authorized three sequential sanity runs: C6 N3 mask238 with two ANDs returned UNSAT (0.0097s); the same graph with three ANDs returned SAT (0.0114s); N4 mask13726 with four ANDs returned SAT (0.0088s). All matched expectations. The SAT witnesses were scalar-checked by the encoder on all64/256 assignments, then checked again by a separate set-based evaluator including read-back indexes, all singleton inputs and every output assignment. Both witnesses also happen to have all ANDs implying the final edge function. The latter cleanliness is observed for these witnesses only, not a consequence claimed for arbitrary circuits. See sanity-independent-verification.json for hashes and results.

Command, from /workspace/pequalnp-proofs:

```sh
python3 results/search3457/free-or/free_or_and_sat.py --N 4 --mask 13726 --ands 3 --seconds 120 --solve --outdir results/search3457/free-or
```

The default solver path is the pinned local Lean toolchain CaDiCaL2.1.2; change --solver when reproducing elsewhere. Each solver process has256MiB address-space cap,120-second internal time limit and125-second external wall limit. Default solver seed0. Complete stdout, stderr, wrapper logs, CNF, mapping, solution status and result JSON are preserved.

Sanity reproduction commands:

```sh
python3 results/search3457/free-or/free_or_and_sat.py --N 3 --mask 238 --ands 2 --seconds 120 --solve --outdir results/search3457/free-or
python3 results/search3457/free-or/free_or_and_sat.py --N 3 --mask 238 --ands 3 --seconds 120 --solve --outdir results/search3457/free-or
python3 results/search3457/free-or/free_or_and_sat.py --N 4 --mask 13726 --ands 4 --seconds 120 --solve --outdir results/search3457/free-or
```
