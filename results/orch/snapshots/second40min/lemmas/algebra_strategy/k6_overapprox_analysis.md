# k6 all-positive candidate analysis

The frozen 26-gate candidate `../circuit_search/k6-all-positive-best.json` computes exactly

`x1 OR (x0 AND N0) OR (x2 AND N2) OR (x3 AND N3) OR (x4 AND N4) OR (x5 AND N5)`.

Its first nonlinear block is `(x0 OR x1) AND (N0 OR x1)`, which equals `x1 OR (x0 AND N0)` by absorption. Replacing this block directly saves one gate. The normalized 25-gate representatives for every point are saved by circuit_search.

The exact minimal-monomial census is in `k6_overapprox_monomials.json`. All twelve pool signatures are dropped-factor stars: six have one point singleton plus the other five row stars, and six have the four line singletons of one row plus the other row stars. None has extra quadratic or higher-degree minimal error monomials. This census used complete antichain propagation of monotone AND/OR gates, independent of the 76-test signature.

## Why three added output gates still cannot repair the 25-gate form

Fix the other five point variables false. Every old wire becomes zero, the bare selected point variable a, or a line-only union containing at most one designated line from N_a. (Distinct rows meet in exactly one line.) The exact repaired output on this restriction is a AND OR(N_a).

For each of the four designated-line singleton positive assignments, the output's new subcircuit must access an existing wire carrying that line singleton, since the restricted a-only wires have identical values on every such assignment and on the all-lines-false negative assignment. One existing line-only wire carries at most one designated singleton, so at least four distinct line-bearing existing wires are necessary.

At least one additional pure-a existing wire is also necessary: otherwise set a=false and all lines=true; every nonzero line-only leaf is true, and any monotone expression accepting a positive assignment would remain true. A connected binary DAG with at most three new gates accesses at most four distinct old-wire leaves, but this repair requires at least five. Therefore any output-only repair requires at least four added gates, returning to the 29-gate baseline.

This is an analytic argument, not a new checked Lean theorem. It does not exclude internal rewiring. A successful 28-gate repair must repurpose old line-OR structure while preserving the other rows' edges; merely appending a guard cannot work.
