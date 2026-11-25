# L-meta-2962 independent dependency review

Reviewed the exact desk statement and local definitions on 2026-11-25. No Lean compilation performed by this agent.

## Definition corrections

- `Core.IsCore` says **not both** operands are implicant gates. It does not say both operands are non-implicant.
- `Core.coneSet n C j` contains `j` itself and all earlier gates in its strict cone.
- `maximalCores` ranges over all circuit gates, including dead gates. The lift-fixed-point condition only controls lift sites in the output cone.
- `gammaE G C j` is a filtered subset of `G.edgeFinset`.

These distinctions matter for any attempted counting argument.

## Existing related files

No existing proof or reduction of L-meta-2962 found. Relevant adjacent refutations already present in the repository:

- `L_meta_2969.lean`, 43 lines: disproves the companion total-gate count, using two shared copies of `(x0 AND x1) AND (x0 OR x1)`, one dead. This does not directly refute our inequality.
- `L_meta_3444.lean`, 79 lines: disproves an exclusive-cone companion bound on a five-vertex path.
- `L_meta_3446.lean`, 105 lines: disproves the exclusive-cone variant of our cover inequality even when all gates are live. It uses a seven-vertex graph with edges 02,03,14,56 and a 17-gate circuit. Its original, unfiltered cone union is larger, so its numerical contradiction does not immediately transfer.
- `L_meta_3652.lean`, 822 lines: under additional liveness and no-implicant-operand conditions, every double-reread edge lies in a maximal core's accepted-edge set.
- `L_meta_3657.lean`, 279 lines: under additional structural conditions, a gate is implicant precisely when all its later containing gates are OR gates.

Importing these Outside files is not permitted by this gap. Useful proofs would need copying into the single allowed file.

## Small components and a potential cut

The following are independently achievable mathematical components:

1. The accepted-edge union D is contained in G.edgeFinset.
2. Every maximal core belongs to the union U of its cones, so mc <= |U|.
3. Distinct maximal cores do not lie in each other's strict cones.
4. If maximalCores is empty, D=U=empty and the target follows because T and T' are minimum covers of the same graph.
5. For any edge set D, a cover S of the graph consisting of D and a cover T' of G-D give a cover S union T' of G. Thus tau(G) <= tau(D)+tau(G-D).

Consequently a sufficient circuit-only bound is |D|+tau(D) <= |U|+mc. This isolates the shared-cone resource-counting difficulty from ordinary cover extension. It is stronger than the posted statement and is not proved here. A two-hypothesis reduction could use cover extension and this circuit bound, but the lease does not advertise reductions_open; parent must not assume reduction submission is eligible.

Beware invalid simplifications: a core can accept a non-star edge family, so tau(D)<=mc is not automatic. A core with a large accepted star can have only about |D| gates in its cone, so the coarser sufficient bound 2|D|<=|U|+mc is false in general.
