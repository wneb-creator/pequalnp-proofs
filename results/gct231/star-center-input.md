# Full-star equations with the center diagonal eliminated

This is an invertible affine change of the same 18 coefficient parameters. For each basis direction, the old center-diagonal coefficient is replaced by the negative sum of the three new leaf-diagonal coefficients and twice the off-diagonal coefficient sum. The formerly eliminated diagonal33 is free with coefficients n0,n1,n2; diagonal00 now enforces the tangent equation. The three incident off-diagonal pivots remain x,y,z.

The variable order groups each direction's three leaf-diagonal coefficients followed by its three free leaf-edge coefficients. There are still exactly 31 equations in 18 variables; the expanded coefficient polynomials now contain 3600 terms. This is a coordinate change, not a dimension reduction or a claim of improved runtime.

Independent review checked the affine inverse in both directions, all 16 matrix entries, symmetry and tangent constraints, all 31 forward/inverse polynomial identities, and independently reconstructed the coefficients with Ryser's permanent formula. Both actual rational and F1009 sparse inputs match the exact primitive source polynomials. Solver runs using this input are recorded separately.

The frozen 14-file `star-center-input/` archive has manifest SHA256 `43db6c750a8cc63f367d566ff5b54ebcc02109c45eaaff5c816be1c9f2c0542d`.
