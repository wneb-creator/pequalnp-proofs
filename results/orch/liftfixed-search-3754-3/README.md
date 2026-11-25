# L-meta-3754 finite circuit searches: checkpoint 3

This continues ../liftfixed-search-3754 and ../liftfixed-search-3754-2. No posted proof or refutation has been found. Z3 UNSAT is recorded as a finite solver result without a kernel-checkable certificate; UNKNOWN is only a timeout. Exact-size and selected-q queries do not by themselves establish a global minimum or exclude smaller sizes.

## Stronger bypass constraints

A globally minimum circuit cannot have a gate replaced by either parent while preserving the target: deleting that gate would give a smaller circuit. Replacing an OR by one parent only decreases output, so some graph edge input must be lost. Replacing an AND by one parent only increases output, so some maximal independent-set input must become accepted. The complete extremal sample set therefore detects either required change. The new scripts add both local bypass tests for every prefix gate, in addition to whole-gate-to-zero criticality. Clean terminal ANDs automatically satisfy the bypass requirement because each parent is dirty and their outputs feed a final OR. SAT reconstruction checks every gate and both bypasses on the complete truth table.

The root agent has separately compiled these necessary conditions in root-bypass-checked.lean (129 lines, SHA256 dd6c1393082c175ec88317add5294d6b85e553f0ef6a46d5b0094b631c3d515e). That Lean artifact is preserved separately from this search bundle. The scripts do not rely on an unproved heuristic for these constraints.

## General dirty-prefix normal form

`dirty-normalform.py` generalizes the preceding exactly-one-dirty encoding. Arguments are graph JSON, exact size m, number q of clean terminal ANDs, timeout milliseconds, and optionally the exact dirty-AND count d. Omit d or use zero to allow any positive number of dirty ANDs.

For a least lift-fixed circuit, a clean wire cannot feed any AND or a dirty OR. Thus every dirty gate can be placed in a prefix; q clean AND gates read only prefix/raw inputs; clean ORs form the final output network. Its q indispensable terminal signals require and suffice for q-1 OR gates. Hence the prefix has L=m-2q+1 gates, all dirty. If d of them are ANDs, p=L-d are ORs. Structural separation and its extension from one dirty AND to arbitrary d were independently reviewed by the root and status-review agents. The interpretation still assumes leastness and exact m; SAT models must receive a separate global-minimality argument before becoming posted refutations.

The matching4 seven-gate, two-dirty-AND positive control passes full truth-table, lift-fixed, criticality, and both-parent-bypass checks. Its clean minimum is at most three gates, so these necessary local constraints alone do not imply leastness.

## Failed auxiliary conjecture and explicit obstruction

An exploratory conjecture said that all exceptional three-edge clean terminals using one dirty gate would have the same P4 support. `one-dirty-terminal-audit.py` disproves it. The audit stops after ten counterexamples; its log reports the exact examined count and is not a full exhaustive classification.

The included hand-constructed 13-gate C8 model sets h=x0 AND (x1 OR x4 OR x7). Its clean terminals are (h OR x2) AND (x1 OR x3), (h OR x6) AND (x5 OR x7), and x4 AND (x3 OR x5). Their edge supports are respectively {01,12,23}, {56,67,70}, and {34,45}; their OR computes C8 on all 256 assignments. This refutes only the auxiliary support claim. The model is not minimum: the first OR(x1,x4) may bypass to x1 without changing the output. This observation motivated the stronger bypass tests above. The model file and independent verifier check that bypass explicitly.

## C8 one-dirty subcases

At exact size 11, the one-dirty normal-form queries with q=3,4,5 are all UNSAT (q3 took 170.406s). The ordinary mathematical bound that a circuit with A AND gates has at most 2^A maximal false assignments excludes q<3 here, because C8 has 10 maximal false assignments and A=q+1. This maximal-false bound has not been formalized in this bundle. The conclusions are specific to exactly one dirty AND and the stated exact size; they are not the posted theorem.

## Completed queries

| Query | Result | Seconds |
| --- | --- | ---: |
| cycle8-size 11-dirty-normal-d0-q4 | UNSAT | 3.193 |
| cycle8-size 11-one-normal-q3 | UNSAT | 170.406 |
| matching4-size7-dirty-normal-d2-q1 | SAT | 0.688 |
| path4-size5-one-bypass-q1 | SAT | 0.141 |
| theta2449-size13-one-bypass-q4 | UNKNOWN | 180.096 |
| theta2449-size13-one-normal-q4 | UNKNOWN | 120.052 |
| theta3338-size12-one-bypass-q4 | UNSAT | 123.9 |
| theta3338-size12-one-normal-q3 | UNKNOWN | 180.014 |
| theta3338-size12-one-normal-q5 | UNSAT | 3.503 |

Checkpoint created 2026-11-25T17:48:00.095993+00:00. Active searches excluded. Source/graph dependencies remain in the earlier bundles.
