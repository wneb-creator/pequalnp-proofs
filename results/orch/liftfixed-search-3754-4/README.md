# L-meta-3754 finite circuit searches: checkpoint 4

This continues the three earlier liftfixed-search-3754 bundles. No posted refutation or general proof has been found. All negative solver results are computational, without a Lean UNSAT certificate. Exact-size, q, dirty-count, and reader-cap restrictions are recorded in the filenames and logs.

## Structural and cardinality refinements

`dirty-normalform-pruned.py` adds only redundant necessary properties of a least circuit to the reviewed general normal form: distinct parents; every incident raw input and every prefix gate has a reader; every prefix gate accepts some edge; and the first prefix gate is an OR. A raw AND is either clean (its two inputs are an edge) or accepts no edge, so cannot be a dirty edge-critical first gate. Bypass tests explicitly require an OR bypass to lose an edge and an AND bypass to accept a maximal false input. The status-review agent read and approved this complete source.

`dirty-normalform-counted.py` replaces the optional exact dirty-AND pseudo-Boolean cardinality with a bitvector sum whose numeric range exceeds the largest possible count. It changes the encoding, not the constraint. `dirty-normalform-readers.py` additionally caps each raw input's number of distinct direct reader gates; only explicit cap3 queries are included here.

The cycle reader cap3 has an ordinary mathematical justification: setting a vertex false deletes all of its direct reader gates through constant propagation/unary bypass. C8 then computes P7 with an isolated input; P7 has7 maximal false assignments and6 edges, giving AND≥3 and OR≥5, hence size≥8. Therefore an11-gate C8 candidate has at most3 readers of that raw input. C10 similarly reduces to P9, whose12 maximal false assignments and8 edges give size≥11, again leaving at most3 readers. The finite cofactor counts and induced edge≤vertex checks are included. This particular compression-to-reader-count bridge is not a compiled theorem in this bundle; reader-restricted exclusions retain that mathematical scope.

The accepted pseudoforest OR floor and maximal-false AND floor force exactly4 ANDs at the C8 optimum11 and exactly5 at the C10 optimum14. Accepted L3760/L8725 exclude exactly one dirty AND in a least bipartite C4-free circuit. Thus the actionable C8 cases are (dirty3,clean1) and (dirty2,clean2); both unrestricted exact-count Z3 queries timed out300s. The analogous C6-with-one-leaf minimum9 has exactly3 ANDs, leaving dirty2/clean1 as the only multiple-dirty case; that query returned UNSAT75.34s. These statements depend on the stated accepted/formal lower-bound ingredients and do not constitute a proof of the posted universal theorem.

The cofactor JSON reports conditional numerical floors from maximal-false count and pseudoforest OR count. A weaker floor in that JSON is not a claimed exact minimum. In particular adjacent leaves on C6 have cover4 and accepted L217/L2399 force4 ANDs, stronger than their7-maxfalse count alone.

## Independent Cadical route and conversion validation

`bitblast-cadical.py` reads a saved QF_BV SMT2 query, applies simplify/bit-blast/Tseitin-CNF, saves the complete DIMACS, and runs the installed Cadical with proof output disabled. Complete solver stdout/stderr are retained. Before reporting a SAT circuit it checks every DIMACS clause, explicitly builds a Boolean model for every internal bit-blast atom, applies the stored model converter, verifies every original SMT assertion, reconstructs gate indices, and evaluates the circuit on every Boolean input. Graph bipartition/C4-freeness, lift fixedpoint, a dirty AND, every gate-to-zero edge witness, and both local parent bypasses are independently checked.

The explicit internal-atom interpretations matter in the installed Z3 5.3.3: a fresh ordinary Solver model omitted these internal constants, and naive conversion did not satisfy the original three-bit probe. `bitblast-conversion-probe.py` records this behavior and verifies the corrected construction. No result from naive conversion was accepted.

The matching7 positive control produced a 770,605-byte CNF and Cadical SAT. The recovered model passes every CNF clause, every original assertion, and all16 full truth inputs. Its original SMT query, full CNF, complete solver logs, model, and metadata are included. This is a nonminimum7-gate matching circuit, not a posted counterexample. The larger Cadical runs were active and are excluded from this checkpoint.

## Completed Z3 queries

| Query | Result | Seconds |
| --- | --- | ---: |
| cycle10-size14-dirty-counted-d2-q3 | UNKNOWN | 180.29 |
| cycle10-size14-dirty-reader3-d3-q2 | UNKNOWN | 180.254 |
| cycle8-size11-dirty-counted-d2-q2 | UNKNOWN | 300.345 |
| cycle8-size11-dirty-counted-d3-q1 | UNKNOWN | 300.306 |
| cycle8-size11-dirty-normal-d0-q2 | UNKNOWN | 180.054 |
| cycle8-size11-dirty-normal-d0-q3 | UNSAT | 146.161 |
| cycle8-size11-dirty-pruned-d0-q1 | UNKNOWN | 180.078 |
| cycle8-size11-dirty-pruned-d0-q2 | UNKNOWN | 180.069 |
| cycle8-size11-dirty-reader3-d2-q2 | UNKNOWN | 181.53 |
| cycle8-size11-dirty-reader3-d3-q1 | UNKNOWN | 181.438 |
| cycleleaf7-size9-dirty-counted-d2-q1 | UNSAT | 75.34 |
| matching4-size7-dirty-counted-d2-q1 | SAT | 0.099 |
| matching4-size7-dirty-pruned-d2-q1 | SAT | 0.176 |
| matching4-size7-dirty-reader3-d2-q1 | SAT | 0.477 |
| theta3338-size12-dirty-normal-d0-q4 | UNSAT | 100.312 |
| theta3338-size12-dirty-pruned-d0-q3 | UNKNOWN | 180.031 |

Checkpoint created 2026-11-25T18:11:17.723588+00:00. Graph/source dependencies not repeated here are in the earlier bundles or cycle-extrema-3754.
