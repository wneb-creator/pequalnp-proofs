# Independent C4 open-case elimination review

Verdict: PASS for the necessary-equation reduction, geometric normalization, and the four unsquarefreed exact certificate inputs. This is an algebraic and mathematical review, not a Lean result or a whole-gap exclusion.

Scope: the nonzero-product C4 branch, permutations 0 and 1, with `beta*gamma != 0` and `det_W != 0`. The remaining permutations, degenerate boundaries, coordinate-factor-zero branch, and arbitrary support planes are separate obligations. The quadratic/cubic formulas are the previously reviewed C4 coordinate formulas.

I independently recomputed the two Gram matrices, their determinants, orthogonality of the normalized extension vector, and the coefficients of `c(k+t*w)` by direct substitution. This agrees with all five used source equations (`q_w`, `c_w`, `normal_q`, `normal_R`, `normal_L`). In particular, the last equation is the coefficient with two copies of the extension vector, not its first polar coefficient.

The geometric necessity argument in `results/gct231/c4-nonzero-normalization.md` is sound: inside nondegenerate W4, the isotropic two-plane K satisfies K-perp = K. The W4 component of an extension vector lies in K and can be subtracted. The quadratic dual of the third graph relation lies in K, so its adjugate-scaled vector also lies in K. Evaluation of the cubic's two mixed coefficients at that vector gives normal_R and normal_L. This uses polarization over characteristic zero. No claim is made that an arbitrary three-plane has the fixed C4 support.

After substituting alpha = 1/(beta*gamma), the exact determinant is

    3*(2*beta^2*gamma^2-1)*(beta^2+beta-1)/(2*beta^2*gamma^2).

Every numerator or denominator factor discarded in either case is supported by beta, gamma, `2*beta^2*gamma^2-1`, or `beta^2+beta-1`. Their nonvanishing follows from the stated open conditions. The division by v in normal_L is used only in the v-nonzero branch. The product-scales equation becomes zero identically. Omitting square_cubic weakens the necessary system and is valid for an exclusion attempt.

The independent checker does not call `resultant`. It reconstructs linear-versus-polynomial resultants from `sum(P_j*(-b)^j*a^(n-j))`, and the even-quadratic pair resultant from `(A*D-B*C)^2`. All six resultant polynomials agree with the exports up to explicitly logged allowed factors. Their generic degrees are positive (1, 2, or 3), and no leading coefficient is divided out. Hence specialization, including vanishing leading coefficients, preserves the required implication from a common finite root to a zero resultant.

All four actual flat and sparse QQ certificate inputs were parsed independently and matched term for term, including ordering and original multiplicities. The v-zero inputs have two variables, four equations and 145 terms. The v-nonzero inputs have three variables, five equations and 254 terms; their additional equation is exactly `inverse_det*saturation_nonzero - 1`.

The earlier squarefree QQ basis reports are consistent with the stated contradiction: in case 0, beta = -gamma and gamma^2-gamma-1 = 0; in case 1, beta = gamma and gamma^2+gamma-1 = 0. Both force the excluded beta^2+beta-1 = 0. Taking squarefree parts preserves complex zero sets but not ideals. The new certificate inputs avoid that distinction entirely. This review does not independently certify the earlier Gröbner computations; exact traces/certificates for the new inputs remain a separate step.

Evidence: `check.py`/`check.log` (both cases and all four inputs, exit 0), `geometry.py`/`geometry.log` (direct coefficient checks, exit 0), and `checked-source-hashes.json`. No source, input, or named Lean file was changed.
