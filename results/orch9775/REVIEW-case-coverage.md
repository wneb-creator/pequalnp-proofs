Independent case-coverage review: PASS, with final Lean assembly pending.

The exact nineteen edges in UpstreamGraph match L-meta-9775, including (1,9) and excluding (2,12). I parsed the finite weights and mask lists directly from the Lean source, then evaluated `possible` on every integer mask from 0 through 16383 independently. No mask survives cap9; exactly [127,1290,4757,8488,16256] survive cap10; exactly the listed117 masks survive cap11. No extra finite completeness premise is needed.

For a normalized circuit of length at most24, the surplus identity gives Bplus+Bzero<=11. WeightClassification supplies Bplus>=10. Thus there are exactly two arithmetic cases: Bplus=10 with Bzero<=1, or Bplus=11 with Bzero=0. The cap10 residual-unit counts are respectively3,0,2,0,3. These equal Bplus+|I|-14, including the six-element mixed mask4757. The cap11 count is |I|-3, which is nonnegative on every surviving mask.

All four supplied permutations are bijections of the fourteen vertices and preserve every edge and nonedge. They form a group. I recomputed all37 orbits from the exact graph and verified that their disjoint union is exactly the117 cap11 masks. Removing the pure-side orbit [127,16256] leaves36 certificate orbits. The JSON audit records, for every original mask, a permutation sending that mask to its representative; this explicitly fixes the required transport direction.

The complete raw solver results show UNSAT for all115 cap11 nonside masks; the two SAT layouts are the pure-side cases separately excluded by the checked side/private-bound lemmas under Bzero=0. At cap10, the two zero-residual cases1290/8488 are UNSAT under weak rules, and the other three are UNSAT under paired-exact rules valid for Bzero<=1. These solver results are computational evidence only until their generated resolution proofs compile in Lean. The certificate metadata uses the correct residual count in each case.

No direct use of the new upstream theorem for the different graph is justified: its four degree-two vertices induce one edge, while this graph's degree-two vertices induce none. The adapted generic lemmas and regenerated finite data avoid that mismatch.

Exact hashes, exhaustive checks, permutation transports, and solver metadata are in case-coverage-independent.json. The eventual permutation lifting theorem and final assembled proof must still be reviewed at their final hashes.
