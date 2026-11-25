# Existing 13-AND lower bound: scope audit

The existing theorem [L_meta_1898](../../../lean/PEqualNP/Outside/L_meta_1898.lean) at line 7314 proves that an ordinary monotone circuit passing the stated difference-incidence positive and independent negative tests has at least 13 actual AND gates. Its explicit hypotheses contain no ReadK restriction. The fully qualified final theorem stands outside the closed helper namespaces.

For a fully correct incidence circuit, every required positive test is an incident pair. Every required negative assignment selects a point subset and only lines adjacent to none of those points, so it is independent even without the theorem's additional closure qualifiers. The independent audit checked this for all 8,192 point subsets.

Replacing each primary line label l by -l modulo 13 carries the sum-incidence function to the difference-incidence function. It leaves all gate operations and their count unchanged. The audit also checked the exact 52-edge correspondence. Thus the existing theorem applies mathematically to the sum-incidence function in L-meta-2056.

An AND-record model with K records expands into at most K ordinary AND gates; the other inserted gates are OR gates, and cleanup can only delete AND gates. Consequently the global K=12 configurations and their prepared successors are known impossible. Their encoding/control audits remain valid infrastructure, but those configurations are superseded and must not be described as ready for a useful search. This conclusion comes from the existing theorem, not an external solver UNSAT result.

This audit is not a new Lean theorem or compilation. It gives no 64-total-gate lower bound, no 63-gate witness, and no resolution of the posted gap. K=16 bounded-membership and general 63-gate searches remain relevant. Exact source hash, original theorem header and finite audit details are in [the scope record](L1898-ordinary-and13-scope.json).
