# C4 scaled coordinate interface: independent source and algebra review

The snapshot of `fresh/C4CoordinateInterface.lean` with SHA256 `6a377895f62788e7126b35e93505ebe0a7586358bf83fecfa6a1374428ae99dc` passes independent review of its matrix and coefficient formulas. Every one of its 16 entries equals eight times the previously reviewed inverse coordinate map. The matrix is symmetric, has zero entries 02 and 13, and has total entry sum zero.

The Lean `quadratic` and `cubic` definitions agree exactly with the corrected Q4 and C16. Independently recomputing the permanent with Ryser's formula gives

`per(J + z*scaledMatrix) = 24 + 16*Q4*z² + 32*C16*z³ + per(scaledMatrix)*z⁴`.

Scaling back to the actual matrix `T = scaledMatrix/8` therefore gives quadratic coefficient Q4/4 and cubic coefficient C16/16. At e=0 the cubic is exactly `2*(f*a*b − H*X*Y)`. The 24 terms displayed in the Lean `perm4` statement contain every permutation exactly once.

Standalone source and complete log: `/tmp/oec/pequalnp-pilot-75/gct231/fresh/c4_scaled_interface_review.py` and `fresh/c4-scaled-interface-review.log`. Completed 2026-11-25T11:36:21.091378+00:00. This independent check used exact symbolic arithmetic and did not launch a Lean compiler or change the author source. It validates the formulas and snapshot lineage; the author's Lean build remains separate.
