# Independent bounded-family script review

Reviewer: library_route, 2026-11-25. Scope: source-level mathematical and arithmetic review. No exhaustive search was rerun, and the reported direction/orbit counts are not independently recounted here. This is not a global nonexistence argument or a Lean proof.

Reviewed source SHA256 values:

- small_entry_families.py: `11cec6fee0090e9ade119a9c7ba964c85b9db221cb5f9cb3f7a192bca8efcf4c`
- small_entry_families2.py: `891a9b0878ca0afd5ed7c6d53a177460a21df22d54f6cadc29d06780c75ec209`
- small_entry_families3.py: `dc44eb6af408961743ea81a826aa64e805f850b5813a983a51b150838be4890c`
- gaussian_families.py: `66c7b47e6e52150c231c3df3ba4075e09eb8b6e30342cc1fe784cb20c51f5fc1`

Verdict: PASS for the explicit bounded search scope.

The ten coordinates are the symmetric upper-triangular entries in lexicographic order. The polynomial is generated directly from all 24 permutations. Vanishing of its four homogeneous coefficients is exactly the condition that the entire scalar line has permanent 24. Bounds 2 and 3 enumerate all six off-diagonal and three initial diagonal entries and determine the final diagonal from the total-entry condition, retaining only final entries inside the original box. This covers the full stated bounded domain. The Gaussian unit alphabet uses the same elimination and retains exactly entries 0, ±1, ±I.

Integer gcd and sign normalization leaves one representative for every rational line in the box; distinct primitive representatives cannot be complex-proportional. Gaussian normalization multiplies by the conjugate of the first nonzero entry, a unit, and deduplicates the resulting vectors with first nonzero entry 1. Thus distinct Gaussian representatives are also linearly independent in pairs. Wedge normalization correctly identifies rational planes up to scalar and coordinate permutation. The minor-based triple-independence test implements Cramer's rule without division.

For a pair of constant directions A,B, the degree-k restriction to their span has no pure terms. For degree 2 one mixed coefficient remains; for degree 3 two remain; for degree 4 three remain. Evaluation at A+B, A−B, A+2B determines all of these coefficients, since the corresponding interpolation matrices are invertible over complex numbers. Hence the pair compatibility tests certify the whole complex plane, not merely three sample points.

For three pairwise compatible directions, every monomial supported on at most two coordinates already vanishes. The only remaining cubic term is xyz, tested at A+B+C. The only remaining quartic terms are x²yz, xy²z, xyz². The three evaluations at coefficient vectors (1,1,1), (−1,1,1), (1,−1,1) give an invertible matrix on these three monomials, so the tests are sufficient for the entire three-dimensional family.

The arithmetic bounds are far below int64 limits. With integer entry bound 3, every pair/triple test entry has absolute value at most 9, and the total absolute quartic monomial contribution is at most 24·9⁴ = 157464. Lower degrees and minor tests are smaller. Gaussian real/imaginary paired multiplication uses only integer additions and products; original entries have complex norm at most 1 and test combinations at most 3. Even conservative bounds on the component arithmetic are below the integer bound above. The preliminary diagonal sums are also bounded. There is no floating-point arithmetic in the Gaussian evaluator.

No completeness claim beyond these explicit entry alphabets follows: a general complex three-dimensional family need not contain a basis in any of the searched bounded sets.
