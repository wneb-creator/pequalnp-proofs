# Focused reassessment of pair-clean normalization

No complete route or counterexample to L-meta-3457 was found in this pass. The following are exact obstructions to two tempting local approaches.

1. Pair-cleanliness does not avoid the global lower-bound implication.

The existing masking reduction gives a singleton-clean equivalent of every backwards-reading monotone incidence circuit with additive 4N−1 gates. The exact target of L3457, despite allowing same-part pairs and larger independent sets inside AND wires, suffices for checked L3447: |E|≤5*D.size+1. Hence any general size-preserving pair cleanup still implies |E|≤5*C.size+20N−4 for unrestricted monotone incidence circuits. Avoiding the stronger |E|+vertex-cover−1 budget does not avoid this consequence.

2. Allowing same-part terms makes pair tests insufficient to establish function equality.

For the three-edge matching f=p0*l0 OR p1*l1 OR p2*l2, the function h=f OR p0*p1*l2 agrees with f on every singleton and every two-variable assignment. It has a circuit whose every AND is false on singletons and on nonincident cross pairs: compute the three edge terms, the same-part term p0*p1, then its product with l2, and OR the results. Nevertheless h accepts the independent triple {p0,p1,l2}. Therefore a cross-to-same-part replacement that only preserves pair behavior needs a separate argument on larger independent supports. This example is an obstruction to that proof method, not a counterexample to L3457.

3. An earliest dirty gate need not admit an in-place clean replacement from the existing prefix, even for a two-edge matching.

Take f=p0*l0 OR p1*l1 and the seven gates

    a = p0 OR p1
    b = l0 OR l1
    g = a AND b
    c = p0 OR l1
    d = p1 OR l0
    h = c AND d
    output = g AND h.

This computes f; every AND is singleton-zero; g is dirty. Suppose only g is changed, with the preceding and succeeding gates kept fixed, and its replacement is any AND or OR with at most two inputs chosen among p0,p1,l0,l1,a,b.

Since h is true on both real edges, the replacement must be true on both real edges. Since h is also true on both same-part pairs {p0,p1} and {l0,l1}, the replacement must be false on those pairs. Every nonempty OR of available wires accepts at least one same-part pair, while empty OR loses the real edges. For an AND to accept both real edges, each operand must accept both; the only available such wires are a and b. Repeating a or b accepts one same-part pair. Thus the only function-preserving gates are a AND b and b AND a, both dirty. Empty AND also accepts the same-part pairs.

The exhaustive 86-candidate verification over all16 inputs is saved as fixed-prefix-replacement-obstruction.json. The mathematical argument above does not rely on that finite computation. This blocks only a one-gate replacement with fixed surrounding circuit: replacing the entire three-gate prefix by the standard three-gate matching DNF does work. It consequently identifies the relevant issue as paying for prefix/suffix restructuring when old OR computations are shared.

The remaining plausible global route must control larger independent supports and account for shared OR computations while reallocating several gates. No invariant proving this with zero size increase was obtained. The established N≤3 classification and assembly remain valid separate partial progress.
