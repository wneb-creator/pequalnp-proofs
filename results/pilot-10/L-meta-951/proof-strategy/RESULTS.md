# L-meta-951 proof-strategy results

No proof or counterexample to the full posted statement has been found.

## Kernel-checked partial theorem

`Small951.lean` proves `small_lower`, the exact requested lower bound under the additional hypothesis that every target set has cardinality at most three. The file has 481 lines and imports only Mathlib and PEqualNP.Defs. `small951-build.log` is empty; Lean exited 0. The proof generalizes the ownership argument from L_meta_907 to arbitrary finite linear families. It uses one owned gate for a pair and two distinct owned gates for a triple. The sole NOT is antitone and cannot be owned.

The argument also conceptually works with a free arbitrary antitone oracle input: an antitone input cannot be owned. This strengthened version has not been separately formalized.

## Kernel-checked obstruction to extending that count

`GoodObstruction951.lean` appends a concrete example to the small-case development. Lean exited 0; `good-obstruction-build.log` is empty. For S={0,1,2,3} and extra input z, the circuit

    P = z OR x0 OR x1 OR x2 OR x3
    F = P AND NOT z
    C = OR_i (z AND xi)
    output = F OR C

computes OR_S exactly, but only F and the final output satisfy the ownership predicate Good S. Thus the proposed universal count |Good S| >= |S|-1 is false, even with one NOT. This is not a counterexample to the requested gate-count lower bound; the example is intentionally inefficient.

## Counterexample to one-branch conditional counting

Take two disjoint copies X,Y of a k-uniform linear family S_i on n0 points and m0 sets. Let B0=m0(k-1). Define

    h = (AND all X) OR (AND all Y)
    z_v = x_v AND y_v
    P_i = OR_{v in S_i} z_v
    G_Xi = P_i OR x_anchor(i)
    G_Yi = P_i OR y_anchor(i).

Then G_Xi <= OR(X_Si), h AND OR(X_Si) <= G_Xi, and h is true when all variables outside the X-copy target are true. The analogous statements hold for Y. Cost, including h, is B0+3n0+2m0-1.

For the projective plane of order 7, n0=m0=57, k=8, B0=399. This cost is 683; adding a NOT still gives 684 < 798, the sum for both copies. Therefore a lower bound using only this conditional branch and the selector's cost is false. The other branch required for actual OR outputs remains missing, so this does not disprove L-meta-951.

`Conditional951.lean` records generic semantic inequalities and finite geometry for this example. Its first compilation established the finite geometry checks but failed at a trivial conjunction-order simp. That issue was fixed; the second compilation was stopped to free approximately 9.7 GB of memory. The complete file is therefore not reported as checked. It also does not construct the full gate list; the displayed circuit count is mathematical reasoning.

## Coupling that any full proof must use

Write A_i and B_i for the monotone output functions after replacing the NOT output by 0 and 1. Then A_i <= OR(S_i) <= B_i. The common antitone selector imposes the following stronger cross condition: if p <= q and B_j(p)=1 while OR(S_j)(p)=0, then A_i(q)=OR(S_i)(q) for every i. In particular, any spurious upper-branch witness p forces the entire lower branch to become exact after setting all coordinates in p to 1.

Equivalently, in zero sets, inputs are principal downsets A_v={x_v=0}; the oracle's zero set U is an upset, and outputs are principal downsets D_i=intersection_{v in S_i} A_v. Every nonempty expanded monomial U intersect intersection_{v in T} A_v contributing to D_i must have S_i subset T. A missing target coordinate could otherwise be raised while staying in the upset. The only exceptions are empty monomials, namely zero relations U intersect A_T=empty. However, this condition alone is insufficient: the conditional construction above exploits precisely these relations. Exact output also requires U-free monomials to cover D_i outside U.

No sound charging argument for the combined two branches is currently available.

## Additional mathematical small-excess argument (not formalized)

The independent-search agent found, and this agent checked, a refinement using the first consumer of the NOT. Put base=sum_i min(|S_i|-1,2). Suppose there are only base+1 gates and a nonconstant, used NOT. Ownership forces every binary gate to be Good, with exactly one owned gate per pair and two per larger target. Before the NOT all wires are monotone.

Let q be the first gate consuming N=NOT h, and p its other input. If q is an AND and Good for S, its at least two singleton hits force p to be an owned monotone wire for S by linearity; q is not an exact output because q(all ones)=0. If q is an OR and Good for S, its value zero outside S forces p<=OR S, so any owned p again has owner S. A primary-input p cannot work: at outside S plus another S-variable, N stays false and p is false. This OR consumer is not an exact output because q(0)=1.

Thus p, q and the eventual exact output exceed the two-gate quota. If p was already an exact output, its monotone prefix had already exhausted its quota (and a target of size at least four could not yet have been computed with only two owned gates). Constant or unused NOT gates can instead be removed, leaving the monotone lower bound.

Consequently the full requested bound follows when sum_i max(|S_i|-3,0)<=2: this covers two four-element targets or one five-element target, with all other targets of size at most three. This argument has not been formalized in these scratch files and is not the general theorem.
