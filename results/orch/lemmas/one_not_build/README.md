# One-NOT checked components

All four final Lean runs exited 0. Complete stdout and stderr are preserved here; all are empty. Sources are sibling one_not_semantics.lean, one_not_compile.lean, one_not_eliminate.lean, and one_not_petersen.lean. Scratch imports refer to independently checked sibling components; the parent must inline bodies for a single-file submission.

The strongest result is OneNotPetersen.first_adjacent_and_not_lower: a circuit beginning with AND(a,b), where a,b is a Petersen edge, and containing a later NOT of wire10 whose output is directly read by an AND/OR suffix, needs at least20 gates. The intervening prefix may be any legal gates. The proof preserves the prefix, replaces the dominated NOT with true using suffix monotonicity, removes the NOT and at least one directly consuming gate, and applies the checked18-gate bound for circuits beginning with AND of distinct input wires. The semantic domination hypothesis is supplied by adjacent_implies.

This is a restricted subclass of L-meta-2592, not the complete theorem. It does not cover a dead NOT, arbitrary NOT source, or a suffix containing another NOT. No source-index normalization or liveness assumption is implicit. Malformed wire references retain the library default-false semantics through ConstantSweep.

All four files received independent PASS from reduction_design, including the final Petersen component. Lease ownership is managed only by the parent; work paused on the parent notice of HTTP410.
