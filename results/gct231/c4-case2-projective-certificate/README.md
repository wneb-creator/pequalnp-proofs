Compressed scalar norm certificate for C4 case2

The frozen Lean candidate proves only that its two displayed univariate norm equations imply P+2=0 or P^4-2P^3+4P+2=0. It was independently source/identity-reviewed at freeze time, but had not yet been compiled. Build status will be preserved separately. The full necessary chain and C4 geometry are not proved by this file.

A universal affine leading-coefficient factor was divided from the quadratic/quadratic and quadratic/cubic resultants before reduction modulo the scale curve. On a nonzero corresponding affine coefficient this preserves necessity. Extending to the alternative coefficient chart and proving the coefficients cannot both vanish remain separate formal obligations. The resulting norms have degrees112 and140, with gcd (P+2)^2*(P^4-2P^3+4P+2)^14.

SymPy extended gcd exceeded90seconds/512MiB. An isolated GMP-rational univariate Euclidean implementation then produced exact Bezout coefficients in69.97seconds under90seconds/512MiB/16MiB output caps. Its output was independently checked by Python Fraction convolution in1.63seconds; the earlier toy integral/rational controls also passed, and a noncoprime control was rejected. No engine verdict is trusted without the explicit identity. Clearing denominators gives186605 integer-coefficient digits and a1375-digit positive scale. The resulting Lean source is201340bytes.

The first projective-resultant attempt reached the quadratic/quadratic quotient but hit its512MiB cap while expanding a sixth power. A separate polynomial-arithmetic version completed the cubic pair in43.93seconds. Complete successful and failed logs/statuses are included. No executable binaries are archived.

Independent actual-Lean expression review is preserved separately in ../projective-norm-review/. The original complete, independently reviewed CAS chain is in ../c4-case2-resultants/ and ../c4-case2-resultant-review/; it does not rely on this affine-factor compression.
