# L-meta-2583 counterexample exploration

The joint IsReadK recursion faithfully records one proof tree, so the conclusion does not hold trivially for the original circuit. For example, AND(AND(x,y), OR(x,y)) rereads one input in every accepting proof tree; it is semantically xy but not read-1.

No apparent incidence-hypothesis loophole: fix a point p. The other points are partitioned by the lines through p, each part of size q; N-1=q(q+1) forces q+1 lines through p. Pair uniqueness also prevents two distinct lines from sharing two points, and counting forces every line pair to meet once. The hypotheses are the full finite projective-plane design conditions in disguise.

Finite validation, using cyclic line sets:

| q | N | offsets | edges | maximal false inputs | complete critical test inputs | standard read-1 gates |
|---|---|---|---|---|---|---|
| 2 | 7 | 0,1,3 | 21 | 37 | 58 | 27 |
| 3 | 13 | 0,1,3,9 | 52 | 704 | 756 | 64 |

The validation script checks all line cardinalities and unique lines through point pairs. For q=2 it also exhausts all 16384 assignments and confirms the 27-gate standard circuit and the mintrue/maxfalse coverage. For q=3 it checks every critical assignment but does not enumerate all 2^26 inputs. Agreement on minimal true and maximal false assignments is logically sufficient for monotone circuits.

Files: lemmas/counter_validate.py, lemmas/counter_fano_search.cpp, lemmas/counter_q3_search.cpp. These are exploratory programs, not Lean proofs. Full stdout/stderr are under /tmp/oec/pequalnp-pilot-143/counter-*. The stochastic searches test 26 gates at q=2 and 63 gates at q=3. They do not provide exhaustive lower bounds.

## First search results

The q=2 stochastic run completed 2,603,749,153 tested mutations across 26,038 restarts in 180 seconds. The q=3 run completed 231,298,305 tested mutations across 2,313 restarts in 180 seconds. Neither found a correct circuit; both best candidates miss exactly one edge. These are not exhaustive lower bounds.

A complete critical-assignment SAT encoding is in lemmas/counter_fano_cnf.py. At q=2 with 26 gates it has 5,928 variables and 155,371 clauses. It encodes all binary AND/OR gates, ordered operands, every gate feeding a later gate, and every essential input occurring. Optional first-gate symmetry fixes the first pair to (0,1), (0,7), or (0,8), the same-color, incident cross-color, and nonincident cross-color orbits of the Heawood graph. A 27-gate instance pinned to the known standard circuit returns SATISFIABLE; the 26-gate instance is currently running. A second run includes the top-form restriction: no below-function AND gate lies below another AND. This restricted search remains sound for finding actual witnesses regardless of its completeness.

## Stopped on lease loss

2026-11-25T15:08:05.145656+00:00 Root reported loss of live lease and directed all work to stop. All owned searches had already ended. Both complete Fano26 SAT runs (unrestricted and TopForm) ended UNKNOWN at their 240-second limits. No counterexample and no exhaustive lower bound was obtained. Full diagnostic logs and validation results have been copied to results/orch/counter-output/. The SAT encoding received independent review from status_audit, who checked the gate truth tables, critical assignments, selectors, liveness, and TopForm semantics.
