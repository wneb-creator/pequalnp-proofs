Independent source and exact arithmetic PASS, 2026-11-25.

Source C4Case2ProjectiveNorm.lean SHA bbb25336dd33dc4cf5e1047020305dc5f646e87eeb98ac847ed40cd3e016a2c0. A new strict AST parser reads the actual Lean Horner expressions, allowing only integer constants, variable P, arithmetic and bounded nonnegative integer powers. Pure Python integer coefficient convolution independently verifies both norm factorizations and the full Bezout identity. This does not rely on the author's C++ output verifier or Horner review helper.

The actual Lean premises equal the frozen JSON norm polynomials of degrees112 and140. They equal G times the two cofactors, with G=(P+2)^2*(P^4−2P^3+4P+2)^14. Actual Lean multipliers of degrees81 and53 exactly match the integer certificate; their cofactor combination equals the positive1375-digit scale and their full norm combination equals scale*G. Both scale occurrences and all remaining proof lines were checked. Format uses only Defs, scoped permitted heartbeat/recursion limits and no prohibited constructs.

Scope: two explicit univariate equations imply P+2=0 or P^4−2P^3+4P+2=0. The source does not claim that these norm equations follow from the original C4 system; that separate affine-coefficient branch argument remains outstanding. No Lean run was performed by this reviewer. This is source/identity approval, with compilation and axiom audit separate.
