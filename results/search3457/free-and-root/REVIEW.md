# Independent review: necessary singleton condition on AND regions

Status: reviewed and executed after fresh root lease renewal; result UNKNOWN after120.047 seconds. This is auxiliary computational research, not a Lean proof.

Author: lower_bound. Independent reviewer: counterexample_search.
Reviewed source SHA256: a5aa6fb271e54a5e32185de3faac34ba30955dc91a6df4d90dcde4ec3d908fb5.

Compared against the previously reviewed unrestricted free-AND encoder. The only semantic restriction added by --singleton-roots is, for each OR operand and each singleton input:

    operand_value implies at_most_one_selected_leaf.

For each pair of distinct selector variables si,sj, the CNF clause is NOT operand_value OR NOT si OR NOT sj. The operand is represented by a signed literal; the neg() helper correctly negates it. Every singleton row is present. The independent scalar witness verifier checks the same necessary property and the full edge function on all assignments.

Why the restriction is necessary: collapse an original circuit's AND-only region to its distinct input/previous-OR leaves. If at least two leaves remain, that region originates at an AND gate, and the original singleton-clean assumption makes its value false on every singleton. Constants and copies can be simplified without increasing OR count. Zero/one-leaf operands are unrestricted, false padding remains available, and both constants remain free. The output conjunction already evaluates false on every singleton because the target edge function does.

This condition is not sufficient for a singleton-clean binary expansion. For example, several selected operands can have empty total singleton-support intersection even though every pair intersects. Allowing such cases enlarges the model, so an UNSAT verdict would still be a necessary OR-count bound for the original circuits. A SAT witness in this model need not translate to a valid singleton-clean circuit. The recorded run ended UNKNOWN, so no lower bound or witness follows.

Prepared N4 mask13726 with seven OR gates:2030 variables,16374 clauses, including7616 additional pair/singleton clauses. The unrestricted source and previous UNKNOWN logs remain separate.

Executed command, after root renewed the lease at02:03:04UTC:

```sh
python3 results/search3457/free-and-root/free_and_or_singleton_sat.py --N 4 --mask 13726 --ors 7 --seconds 120 --solve --singleton-roots --outdir results/search3457/free-and-root
```

The solver exited0 with UNKNOWN status after120.0468 seconds. Full stdout/stderr, wrapper logs, CNF, mapping, solution-status file and result JSON are saved beside this review. No SAT witness exists to validate. The run used the reviewed frozen source, default CaDiCaL seed0,256MiB address-space cap,120-second internal limit and125-second wall guard. No further finite search is planned absent a concrete new route.
