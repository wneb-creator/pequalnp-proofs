Checked case2 nonzero-slope boundary

The standalone Lean theorem states: for the explicitly defined case2 scale equation F, chart determinant numerator W and reduced affine slopes rA,rB, F=0 and P*B*W nonzero imply rA nonzero or rB nonzero. The affine equation r=0 is not a premise. This fills only that boundary condition; the normalized-resultant bridge and the main existence theorem are not asserted.

Case2SlopeBoundary.lean SHA256707e23e11549155ca65fe3d04b607d29d0d0173a277ccafef1c4a5b3c27f5480 compiled unchanged with pinned Lean4.36.0/-j1: exit0, empty full log,7.927830367 seconds,2,017,940KiB sampled peak RSS. Exact source plus only the final axiom query passed in7.900604480 seconds,2,050,504KiB peak. Axioms are propext, Classical.choice and Quot.sound. Both used90s/4GiB sampled limits; no source compiler warning occurred.

The source uses exact polynomial norm identities and explicit integer Bezout identities. Their independent QQ review includes original-source lineage, reduction by8K^3, both norms, coprimeness, the affine slope reduction, and determinant factorization. Original source/data, generator, exact identity coefficients, complete build/audit logs and status files are preserved. The initial independent-review diagnostic compared equivalent Sympy expressions structurally; the final check expands their difference to zero. No mathematical correction was required.

Paths are preserved relative to the scratch root so the algebra checker can be rerun from this directory. The compiler runner records existing workspace/toolchain paths and can be adapted to another checkout. No toolchain/vendor tree or binary is included. Namespace and geometric scope remain explicit.
