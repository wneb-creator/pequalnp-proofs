# Three binary linear factors: source review

Independent source review passes for `fresh/LinearFactorMatchingFull.lean`, SHA256 `eb9de3de6915c657561b3e59966d28fae23cbc3e151f3027c87c0b7fd5c318a3` (9528 bytes). The author build `fresh/linear-factor-full-build01.log` is empty and the frozen metadata records exit 0 at 2026-11-25T11:27:10.255537+00:00. This review did not launch another compiler.

The proof evaluates a nonzero binary linear form at its kernel vector. A vanishing factor on that vector is proportional to the form, with nonzero proportionality constant when the factor is nonzero. Cancellation in the polynomial domain reduces three factors to two; the remaining constant is inverted, forcing the product of the three scales to equal one. All six output permutations match the three source factors in the stated orientation. No distinct-factor or linear-independence assumption is introduced, so repeated proportional factors are covered. The missing explicit nonzero assumption on the third left factor is harmless: the right product is nonzero under the listed assumptions, and the cancellation proof does not need that extra premise.

The theorem concerns equality of products of binary linear polynomials. Its use for a geometric subspace still requires supplying that product identity and the nonzero-factor hypotheses. It makes no global claim about permanent-constant three-planes.

Review completed 2026-11-25T11:34:10.210748+00:00.
