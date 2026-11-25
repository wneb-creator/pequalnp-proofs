# L-meta-1896 orchestration notes

Only the root agent requests and renews leases. The initial lease is no longer live.
Exact statement: results/orch/statement.txt
Public gap fields: results/orch/GAP.json

Target statement: 51 OR gates necessary for monotone fan-in-two circuits accepting order-3 plane incident pairs and rejecting generic maximal false inputs. Three reductions already live; do not assume another reduction is available.

Each strategy uses a separately named notes file in results/orch and scratch files in results/orch/lemmas. Root merges the final single file.

## Current live task: L-meta-2448

Exact statement: results/orch/statement_2448.txt. Public gap: results/orch/GAP_2448.json. Root holds and renews this lease only. Previous L-meta-1896 work is stopped. New goal: least monotone circuit for a triangle-free/C4-free graph having HasStarProfile. Three reductions live, two open PRs.

## Replan after 20 minutes on L-meta-2448

2026-11-25T07:27:23.060902+00:00

- Checked and pushed: minimum-circuit existence; pairwise-meeting/clean-gate star conditions; safe AND bypass and copy deletion; exact C5 witness; downward rewrite criterion; star-cover upper construction and conditional assembly.
- Full theorem remains unproved. Replacing all dirty gates by OR or deleting them is unsound because later gates filter false positives. Ordinary globally-below-output bypass adds no restriction at owning gates: their operands already accept singletons.
- Numerical route: sufficient lower bound |E|+minimum-cover-size−1 ≤ every circuit size; not proved. Existing only-one-junk normal-form results handle special cases, multiple interacting junk gates remain.
- Active new route: false-deletion pivotal edges. Restrict a gate to a common center of all its pivotal edges when that variable implies an operand; preserve other edges by monotonicity. Concrete conditional repair just compiled; need prove sufficient pivotal-star condition for an optimal choice of circuit.
- Counterexample search: no counterexample through six vertices; larger cases UNKNOWN/timeouts, not negative proofs. C5 witness alone Lean-checked. Full search artifacts in search/.
- Checker infrastructure: targeted Lean build works. Actual tools/check-lean.mjs returns missing-full-Mathlib-cache FAULT; measured additional disk shortfall ~3.47GiB. No checker acceptance.
- Latest checkpoint commits: e8bae7bc (named partial), 4ac7dbc9 (C5 and rewrite), 32428976 (cover construction).
