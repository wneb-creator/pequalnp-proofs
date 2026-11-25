# Independent FullStar31 equation-mapping audit

Reviewer: global_normal_form, 2026-11-25 UTC.

Verdict: PASS for the frozen source mapping, mathematics, and helper-file
format. No Lean build was started by this reviewer; the library worker's
separate build determines compilation status.

Reviewed `FullStar31.lean`: 761 lines, 65,775 bytes, SHA256
`1d9ce39dfdf8a03b0c818087bd6d243bf209f89840193cf015b9f47cdb55965a`.
Generator SHA256:
`700c0d623f014b17c69fcdab0b9779043fadeb2f4c9cad6a2acc557b28e6c44b`.
Equation-manifest SHA256:
`202584259db877774232fe3fbbcbd4b65302290a7a6ee3a201b0a195a34a253b`.

The independent reviewer parses the actual Lean matrix, derivative
definitions, generic product formulas, conclusion conjuncts, and proof
cancellation scales. It does not merely regenerate the author's manifest.

All sixteen Lean matrix entries equal one plus the corresponding reviewed
full-star JSON matrix entries, with the same eighteen parameter order. In
particular, the last diagonal entry is exactly the total-entry-sum
elimination; no additional zero-entry or symmetry assumption was introduced.
The displayed permanent expansion contains each of the twenty-four
permutations exactly once.

All thirty-one conclusion conjuncts equal the corresponding original JSON
coefficient divided by its positive integer content. Their order is exactly
the JSON order. The multiindices are distinct and comprise every degree-two,
degree-three, and degree-four monomial in three variables: counts six, ten,
and fifteen. Thus no coefficient constraint is lost or duplicated.

For each derivative operator, the actual nested `pderiv` indices have the
specified multiindex. Independently enumerating choices from the four affine
factors reproduces each displayed product formula, including the
multiindex-factorial multiplicity. Each final `linear_combination` cancels
exactly the product of that factorial and the positive primitive content.
All factors are nonzero integers in the complex field. The inherited
constant-coefficient and additive simplifications preserve these identities.

The theorem assumes exactly the full-star formal polynomial permanent
identity and derives its thirty-one necessary primitive equations. It
asserts neither a solution nor a contradiction for that system, and it does
not itself prove the posted geometric statement. Its imports are Mathlib
and PEqualNP.Defs; all declarations remain in the auxiliary gap namespace.
The reviewed source contains no sorry, new axiom, native_decide, forbidden
root marker, strings, or attributes.

The generator's monomial iteration, positive-content extraction, factorial
calculation, and emitted scale agree with the independently checked output.
No reviewed source or manifest was modified. Complete reviewer diagnostics
are in `check.log`; the independently written implementation is `check.py`.
