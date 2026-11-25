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

## Replan after 45 minutes on L-meta-2448

2026-11-25T07:54:00Z

- Checked and pushed named partial is2715 lines at67ddd24b. It now includes pivotal-edge necessity for every gate of a minimum circuit and a same-size repair for gates with a unique pivotal unordered edge. Separately preserved TwoLeafRepair handles singleton-positive gates with a two-vertex cover of their pivotal edges.
- The remaining bad-gate case has multiple pivotal edges and can have shared OR supports. PrivateSupportLimitation is an exact8vertex15gate Lean witness: triangle/C4-free, ORcount8, edgecount10. Thus the proposed unrestricted ORcount≥edges−1 route is false. It is not a counterexample to the posted existential claim.
- or_gate_bound is formalizing an equal-cost three-gate exchange for a matching CNF block. The whole isolated block can be repaired while keeping shared support ORs. General dirty-component decomposition is unresolved. geometry_route pursues that structural obstacle; library_route checks primary literature.
- Primary literature only establishes the cited C4-free lower bound for single-level circuits. Applying it to arbitrary circuits is unsupported. No full proof or target refutation found.
- Public map refreshed07:51:31 UTC still marks2448 and1035 conjectural. The two formerly open2448 reduction PRs12430 and12779 are now closed without recording: intake says each contributor already had five live reductions. Our assigned desk response lists three live reductions for the step; we will not submit a fourth.
- The lease watchdog is alive;07:49:42 renewal expires08:09:42 UTC. Only root holds/renews this lease.
- A reviewed bounded memfd cache experiment is in preparation to make the unmodified full checker runnable within disk/memory limits. No checker acceptance exists; current checker result is missing-cache FAULT. All compiled source has already been pushed before this infrastructure experiment.
