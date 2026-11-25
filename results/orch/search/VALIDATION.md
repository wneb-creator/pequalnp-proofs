# Counterexample-search validation (pilot 152)

These are computational searches and auxiliary evidence. They are not Lean proofs of L-meta-4970. No actual counterexample to the posted statement has been found.

## Completed exhaustive finite searches

- `counterexample-small-search.py`: all semantic circuit states for p=q=2 through 3 gates, then p=2,q=3 through 4 gates; T=0 and star witnesses tracked. No counterexample. Final 2x3 layer: 47,167 states.
- `counterexample-and-count.py`: every 3x3 C4-free graph with vertex-cover size 3 against every circuit using at most 2 AND gates and unlimited OR gates. No counterexample; 1,415 distinct first-AND functions and 4,465,825 second-AND candidates.
- `counterexample-and-count-3x4.py`: same for 3x4 graphs, 6,197 first functions and 77,214,486 second candidates. No counterexample.

The free-OR normal form is exact for AND count: each AND operand is an OR of inputs and earlier AND outputs. Final output is an OR of AND outputs because the graph function is false on all singleton inputs. Dirty and nonhomogeneous intermediate functions are allowed.

## Completed SMT searches

UNSAT (solver result, not kernel-checked certificate):
- C8 with at most 3 AND gates and unlimited OR gates: 0.133 seconds.
- C10 with at most 4 AND gates and unlimited OR gates: 9.561 seconds.
- Any 4x4 C4-free graph containing the diagonal perfect matching, at most 3 AND gates: 0.486 seconds. Relabeling covers all balanced 4x4 graphs with cover number 4.
- Any 5x5 C4-free graph containing the diagonal perfect matching, T=0, at most 4 AND gates: 22.971 seconds.
- C6 with at most 4 OR gates, unlimited AND gates, and all posted star witnesses: 0.056 seconds.
- C8 with at most 6 OR gates, unlimited AND gates, and all posted star witnesses: 3.859 seconds.

SAT positive control:
- Fixed canonical C6 circuit with 8 gates: SAT in 0.007 seconds. Extracted model independently checked on all 64 inputs, including T=0 and every star witness. This meets, rather than violates, the posted bound. The unrestricted size-8 search timed out; the fixed control checks encoding consistency.

UNKNOWN / timeout, never interpreted as UNSAT:
- C12 with at most 5 AND gates, unrestricted ORs: 120 seconds.
- C12 with at most 5 AND gates and T=0: 120 seconds.
- Any 5x5 C4-free perfect-matching graph with at most 4 AND gates, without T=0: 120 seconds.
- Unrestricted positive-control synthesis for C6 with 8 gates: 120 seconds.

Further completed results (2026-11-25):
- Direct unrestricted C12 size<=16: UNKNOWN after 600.138s.
- Restricted C12 canonical-star prefix, size<=16: UNKNOWN after 180.024s.
- Direct theta8 (three length-3 paths), size<=11: UNKNOWN after 300.035s.
- Compressed exact C12 with<=5AND and T=0: UNSAT 16.329s, using 12 edge plus 29 maximal-independent-set inputs. Without T=0: UNKNOWN 180.013s.
- Direct QF_BV C6 size8: SAT 2.093s, full truth-table verified. Size7: UNSAT 11.778s.
- Direct QF_BV C6 with adjacent-independent-gate ordering, size8: SAT 0.455s, full truth-table verified. Size7: UNSAT 6.084s.

Final completed reruns:
- Direct ordered QF_BV C12 size<=16: UNKNOWN / timeout after 180.062s.
- Direct ordered QF_BV theta8 size<=11: UNKNOWN / timeout after 180.037s.
- Compressed unrestricted C12 with at most 5 AND gates, QF_BV and independent-AND ordering: UNSAT after 271.72s. This query has no T=0 restriction.

All searches in this bundle have finished. No counterexample to the posted statement was found; none of the timeout results excludes a counterexample.

## Encoding and reproduction

Python 3 and Z3 5.3.3 are used. The programs add the session scratch `z3-python` directory to `sys.path`; a normal installed `z3` package also works. No solver binaries, archives, credentials, or environment dump are in this bundle.

Official wheel used: https://github.com/Z3Prover/z3/releases/download/z3-5.3.3/z3_solver-5.3.3.0-py3-none-manylinux_2_27_x86_64.whl
SHA256: 0431023a82278dab706c02a320f63178ee0755fb8f10a5c980f0bfe3c84f6f96
Read and downloaded on 2026-11-25; version verified locally.

Examples (milliseconds for solver limits):
- `python3 and-synth.py 4 120000`
- `python3 and-synth-any.py 5 120000 t0`
- `python3 or-synth-cycle.py 4 120000`
- `python3 posted-synth-cycle.py 3 8 10000 canonical`
- `python3 posted-synth-cycle.py 6 16 600000`
- `python3 posted-synth-cycle.py 6 16 180000 starsfirst`
- `python3 posted-synth-graph.py theta8.json 11 300000`
- `python3 and-synth-extreme.py 6 180000 t0`
- `python3 and-synth-extreme-ordered.py 6 360000`
- `python3 posted-synth-cycle-ordered.py 6 16 180000`
- `python3 posted-synth-graph-ordered.py theta8.json 11 180000`

Direct binary-circuit searches require exactly two earlier operands, AND/OR only, T=0, all posted star witnesses, and graph-function equality on all edge inputs and maximal independent-set inputs. For monotone circuits those tests characterize the entire graph function. A star OR is characterized by true singleton inputs for its leaves and false value on the complement of its leaf set. Every SAT model is independently evaluated on the full truth table before being saved. These mathematical characterizations have not been formalized as a Lean search certificate.

`posted-synth-c12-size16.smt2` preserves the original direct unrestricted query. Files ending `-ordered.smt2` preserve the later direct queries with adjacent-independent-gate ordering. `and-synth-c12-extreme-t0True.smt2` and `and-synth-c12-extreme-ordered-t0False.smt2` preserve the compressed AND-count queries, respectively with and without T=0. Solver time limits are in the commands and logs rather than the SMT assertions. `starsfirst` is an explicitly restricted search with canonical left-star OR gates as a prefix and all later gates used; UNSAT there says nothing about unrestricted circuits.

## Search implementation notes

The selector width was corrected from `(n+m-1).bit_length()` to `(n+m).bit_length()` so future power-of-two total wire counts do not wrap their upper bound. None of the completed cases was affected (wire totals 14, 19, 28).

`posted-synth-*-sat.py` uses Z3's QF_BV solver and removes the redundant minimum-OR-count cardinality hint. `posted-synth-*-ordered.py` additionally orders adjacent independent gates by their operation and operand indices. Any circuit admits such an ordering by selecting a lexicographically least topological gate order; this normalization has not been formalized in Lean. `and-synth-extreme-ordered.py` applies the analogous order to AND gates and requires every AND gate to be used by a later gate or the output. Such runs are still computational evidence only.

The saved positive-control model may be a different verified 8-gate C6 circuit found by the QF_BV search rather than the fixed canonical one; each complete SAT log contains its own exact model.

The AND-count models require nonempty operand ORs, and omit direct input wires from the final OR because every graph edge function is false on singleton assignments. In ordered AND-count searches, unused AND gates are removed; an output duplication AND can pad any smaller circuit to the fixed budget. Exactness of the compressed truth patterns follows from monotonicity: any true graph assignment contains an edge input, and any false graph assignment extends to a maximal independent set. These normalization arguments have been checked mathematically, not in Lean.
