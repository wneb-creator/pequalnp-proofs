# Hybrid monotone cofactor-DAG prototype

2026-11-25 UTC. Constructive. Root authorized a CPU prototype of at most 30 seconds while two SAT searches were active. No desk, Lean build, or git action.

## State and recurrence

A state is a canonical pair `(L,E)`, where L is a set of singleton variables and E is a subset of the target's 21 graph edges. All edges incident to L are removed by absorption. The state denotes the OR of its singleton variables and quadratic edge terms.

For an active graph vertex v, the zero cofactor deletes incident edges. The one cofactor adds the current neighbors of v to L and removes all now-dominated edges. If v is already a singleton term, its one cofactor is true and the recurrence reduces to one OR gate. Otherwise the prototype tries both exact monotone identities:

`F = F0 OR (x_v AND F1)`

`F = (x_v OR F0) AND F1`.

These are valid because the monotone cofactors satisfy `F0 <= F1`. This family allows singleton-containing factors and does not impose the previous two-quadratic-supergraph restriction.

## Sharing and leaves

Every state also has a single-level leaf candidate. For its remaining bipartite graph, the code enumerates vertex-cover choices from subsets of the active left side, including both natural orientations and a bounded selection of minimum covers. Edges are assigned to selected centers, their star circuits are built, and singleton terms are included in the final OR.

Canonical state memoization shares repeated cofactors. Global wire hashing shares OR subsets, AND terms, and arbitrary intermediate functions agreeing on all 58 boundary assignments. Live gate cones are stored as bitsets, so alternatives are compared by actual reachable gate count rather than allocated node count. A newly constructed wire replaces an equivalent existing representative only when its live cone is smaller. Constants are simplified away and never require explicit final gates.

Boundary merging can change a cofactor away from those 58 original assignments, but preserves every final boundary value. The final network remains monotone; target correctness on all minimal-true and maximal-false assignments therefore suffices. The retained best is additionally checked directly on all 16,384 inputs.

## Bounded run

- Two-second smoke test: 180 trials, 2.075 seconds including final validation, best 27 gates, zero truth-table errors.
- Main pass: 1,942 trials, 24.143 seconds including final validation, best 27 gates, zero truth-table errors.
- Trials vary vertex order, recursion depth among 2/4/6/8/10/14, and three vertex-selection rules: fixed priority, high-degree/linear-first, and low-degree/nonlinear-first.

The CPU phase is stopped. The complete bounded run found no 26-gate witness. It does not prove optimality even inside the cofactor-DAG family: vertex choices are heuristic, only selected covers are tried, edge ownership and OR pairing are heuristic, and keeping a cheapest individual cofactor can discard a more globally shareable representation.

## Artifacts and reproduction

Stable files are under `/tmp/oec/pequalnp-pilot-70/constructive/`:

- `cofactor_dag.py`
- `cofactor-smoke.json`, `cofactor-smoke.log`
- `cofactor-run1.json`, `cofactor-run1.log`

The program imports boundary data and the independent full-table checker from `factor_partition.py` in the same directory. It otherwise uses only the Python standard library. The installed interpreter is Python 3.12.14; no packages were installed.

Reproduction command, from the repository workdir:

```
python3 /tmp/oec/pequalnp-pilot-70/constructive/cofactor_dag.py --seconds 24 --output /tmp/oec/pequalnp-pilot-70/constructive/cofactor-run1.json > /tmp/oec/pequalnp-pilot-70/constructive/cofactor-run1.log 2>&1
```

The fixed random seed is 70 by default, but the wall-clock cutoff changes how many trials finish. Logs retain complete stdout and stderr. These files are research artifacts, not a Lean proof or an UNSAT certificate.

## Structure of the 30-row CEGIS seed

Later read-only inspection of lower_bound's `biclique30.json` and `cegis26-hints.iteration-7.json` found the same 26-gate circuit in both. It is entirely single-level. It computes the six right stars at vertices 7 through 12, with x13 additionally ORed into the right factors for vertices 9, 10, and 12. Thus its exact graph is G plus four extra edges from vertex 13 to its four left nonneighbors. No additional high-degree terms occur in this particular seed.

The six-star circuit costs 23 gates. Inserting x13 into three existing right factors costs three more, while a correct separate three-neighbor star costs four more. This explains the candidate's one-gate saving and its false positives.

An independent direct evaluation on all 16,384 assignments confirmed this exact supergraph description: zero errors against G plus the four extra edges, 49 false-positive assignments against G, and zero false negatives. The check took 0.351 seconds and performed no search. Result: `/tmp/oec/pequalnp-pilot-70/constructive/cegis30-structural-validation.json`.

A focused cofactor target is a joint 24-gate implementation of F0 and F1, where F0 is the graph function after deleting vertex 13 and F1 = A OR F0, with A = x1 OR x2 OR x4. The final identity `(x13 OR F0) AND F1` would then use 26 gates. After absorbing A, the remaining twelve-edge graph is the incidence graph between the four left vertices {0,3,5,6} and all six pairs of those vertices. The three vertices in A correspond to the three perfect matchings of this K4.

For example, a 23-gate F0 circuit that already computes A internally would give F1 with one additional OR. Such a circuit would have to go beyond the optimal pair-clean star construction: A has no common-neighbor owner in G minus vertex 13, and the refined clean gate budget charges that large OR support as an extra gate. Circuit_search independently identified the simplification F1 = A OR F0. No joint 24-gate construction is known, and this observation triggered no additional CPU run.
