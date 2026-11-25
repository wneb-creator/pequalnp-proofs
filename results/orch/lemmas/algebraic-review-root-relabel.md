Independent review by algebraic_route

PASS. root-relabel.lean SHA256 ac6d3aa15b9466c338d541dcbb71224d3a204a6fc2c5cde2eca9d3b4fdc87b65 retains the reviewed finite-label prefix unchanged. The new MarkedTrace definition is the ordinary syntactic AND product rule and OR rule, with a singleton input seed.

The trace transport uses the inverse lifted wire permutation while the circuit inputs use the forward permutation. relabel_val supplies exact base evaluations, and liftP_inv cancels operand relabeling in the recurrence. Gate-output indices are fixed, so no derivative values are recomputed or lost. Singleton bases and seeded input labels are both transported forward. The cyclic correctness result explicitly assumes a nonempty circuit so the final output is a gate index, then uses the involution and previously reviewed cyclic incidence equivalence.

The complete standalone logs are empty and the frozen receipt records exit 0. No forbidden trust or format markers occur in the new tail. This is exact relabeling, with no pruning or cofactor restriction.
