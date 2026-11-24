# Nine-point core without private columns

This core selects points[0,1,2,3,4,5,10,12,19] of the posted plane. It is the six-point hyperoval plus the three pairwise intersections of external lines25,32,33. The18 nonempty line columns have degrees2 or3, so none is private and no aggregate input ORs are needed. There are27 inputs,45 edges, and nine degree5 point stars. Standard size53; target52. Appending the twelve remaining full-plane stars and their output joins costs72 gates, so a52-gate local witness would yield124. The separate Lean geometry/certificate/lift work handles formal verification.

Exact tests:45 positive edge pairs;512 raw negative assignments indexed by the nine left bits;359 distinct maximal negatives. The heuristic uses404 positive/maximal-negative signatures, and decoded saved candidates are scalar-checked on all557 raw extremal assignments. The data was independently checked against the posted105-edge graph.

This is the reviewed mixed-OR/interacting-matching search adapted to the asymmetric core. Initial stars use only the nine left points. It cycles1/2/3/4/8 latent AND helpers,1/2/4 primary-only OR helpers and1/2/4/8 interleaved mixed OR helpers. Matching warm starts have59 gates and are above the52 target. The reducer checks valid structural circuits of size<=55 and saves any reduced<=52 witness only after scalar verification. Heuristic error weights are adjusted for the smaller test basis.

Validation: the explicit53-gate baseline was scalar-checked on all557 assignments. Author checks covered960 expanded baseline/mutant circuits and13 full scalar baselines, including eight matching starts. Independent review checked another600 expanded cases and120 scalar baselines, including22 matching starts. All complete logs are saved. The two concrete fixtures have53/59 gates and are not counterexamples.

Planned command, from repository root:
```
python3 results/orch/triangle9-search/SearchStochasticTriangle9.py --seed 14772916 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-triangle9-005
```

No52-gate witness has been found; the new run was queued at snapshot time for the existing global search CPU slot.
