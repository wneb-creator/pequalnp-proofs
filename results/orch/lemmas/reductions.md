# Reduction audit for L-meta-2592

Three reductions are live; a fourth cannot be submitted under the desk cap.

- R_meta_2592_271: binary gate lower bound plus exclusion for 1–4 NOT gates. The binary floor is checked as L_meta_4725. Its 3224-line proof establishes 15 + notCount C ≤ C.size.
- R_meta_2592_408: normalize invalid wire reads, trim to the output, then prove the normalized lower bound. Normalization is checked as L_meta_7389 (305 lines); lower bound is still open as L-meta-7391.
- R_meta_2592_318: cut at the last NOT gate, then prove a monotone suffix separator. Cut is checked as L_meta_8295 (66 lines); separator is still open as L-meta-8297.
- The few-NOT lower bound remains open as L-meta-4727, with further reductions to truth-function programs and signed binary circuits.

## Preserved partial

`reductions_many_not.lean` copies L_meta_4725 under PEqualNP.Outside.L_meta_2592_aux and adds the arithmetic consequence: a FanInTwo Petersen circuit of at most 19 gates cannot contain at least 5 NOT gates. The target expression is copied exactly from our desk statement. Only Mathlib and PEqualNP.Defs are used. Original proof source comments attribute the branch-count argument to L_meta_2165 and L_meta_1549. This is a partial result, not the full gap.

The key count is 15 binary gates: 10 essential input wires plus at least six branching wires, minus one. The branch lower bound follows a graph twin-contraction process in which five rounds leave an edge. Strengthening this to the desired bound needs information about gate semantics beyond this topology count.

Compilation pending root toolchain setup. No claim of a new full proof.
