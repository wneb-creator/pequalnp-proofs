# L-meta-1770 orchestration notes

Only root holds the lease and submits. Append findings with strategy names and UTC timestamps. Scratch Lean attempts belong in results/orch/lemmas; root owns the final Outside file.

Lease acquired 2026-11-25T02:59:42.485Z; original expiry 03:19:42.485Z.

## Structural strategy 2026-11-25T03:02:53.695440+00:00

- Existing R_meta_1770_401 proves bottom-bottom double-junk case with constant 204; leaves bottom-deep/deep-deep. R_meta_1770_1 splits singleton/quadratic behavior. L_meta_3807 solves non-nested junk globally.
- Existing leastness infrastructure (1495 no duplicate gates; 1498 tree of below-F gates; 1499/1501 normalize below-F AND nesting) does not remove dirty AND nesting.
- New scratch Structural.lean proves semantic separation: junk gates OR-reaching opposite sides of a top have incomparable truth functions, witnessed on graph-negative assignments. It uses only IsAO2 and top/junk definitions. Initial Lean attempt awaits PEqualNP.Defs oleans.
- Remaining possible route: every nested opposite-junk pair must have mixed AND/OR paths, since pure OR reach would force comparable truth functions and violate semantic separation. Need an amortized charge to such mixed paths; no linear bound established yet.
