# Independent review of the Witt parameterization

Verdict: the exact frame, graph parameterization in both directions, and complete 32-chart coverage argument in `witt.md` are correct. The generators implement the stated open chart and its lifted version correctly. This review does not establish a witness, a unit ideal, or nonexistence in any chart, and none of these results has been formalized in Lean.

The independent check completed at **2026-11-25 10:16:53 UTC**. Source and full log are:

    /tmp/oec/pequalnp-pilot-75/gct231/fresh/witt_review.py
    /tmp/oec/pequalnp-pilot-75/gct231/fresh/witt_review.log

The log records SHA256 hashes for both reviewed generators, the frame export, and the lifted equation export. The dense twelve-variable permanent expansion was not rerun.

## Tangent space and exact quadratic

Because H is symmetric orthogonal and sends the first coordinate vector to half the all-ones vector, a symmetric matrix T has total entry sum zero exactly when `(HTH)00 = 0`. Thus the nine coordinates in `[0,bᵀ;b,A]` describe the entire symmetric tangent space uniquely.

For a symmetric tangent matrix, the degree-two permanent coefficient is

    tr(T²) - 2 (T1)ᵀ(T1).

The Hadamard change gives `tr(T²) = tr(A²)+2bᵀb` and `(T1)ᵀ(T1)=4bᵀb`. Hence the coefficient is exactly `tr(A²)-6bᵀb`, with the nine weights displayed in `witt.md`. These are bilinear expressions over the complex numbers; no complex conjugation is involved. The reviewer independently obtains the degree-two coefficient by selecting two rows in each permanent summand and checks it against this diagonal form.

The E/F/R frame has Gram matrix

    [0,I,0; I,0,0; 0,0,3I]

and determinant -1/8 in the stated coordinate order. The frame JSON agrees exactly with an independently reconstructed Hadamard basis. In particular, the signs and the factor 1/12 in F are correct.

## Graph formula, converse, and lift

In the E-projection chart, every plane has a unique normalized column matrix `C = E + FB + RZ`. The nonzero E-coordinate block guarantees rank three. Its Gram matrix is exactly

    B+Bᵀ+ZᵀDZ,  where D=3I.

Consequently isotropy is equivalent to `B = K - (1/2)ZᵀDZ`, where `K=(B-Bᵀ)/2` is skew-symmetric. This proves both directions of the graph formula, and also uniqueness of K and Z within the normalized chart. The twelve-parameter count is correct.

In the lift, B is written as K+S with S symmetric. The condition becomes `2S+3ZᵀZ=0`, precisely the six quadratic coefficients, up to their individual nonzero normalizations. Solving these six equations for S recovers the twelve-variable chart without losing or adding solutions.

The generator's sparse-ring expansion correctly chooses the perturbation entry in each selected row of every permanent term. Grouping by the three input-variable exponents extracts the intended homogeneous coefficients. Clearing denominators and dividing each equation by its integer content preserve its zero set. The lifted export has all six quadratic, ten cubic, and fifteen quartic coefficients, with the documented parameter order.

## Complete chart cover

The fourth pair `E4=R1+iR2`, `F4=(R1-iR2)/6` is isotropic with pairing one. The remaining vector R3 has norm three. The reviewer checks all 32 resulting ordered frames exactly. In each, the residual Gram matrix, using the unchosen pair followed by R3, is

    [0,1,0; 1,0,0; 0,0,3].

The stated rank inequality for coordinate-pair groups is valid. If J contains j pairs and their restrictions to a totally isotropic three-plane have rank r, their kernel is isotropic in a nondegenerate `(9-2j)`-dimensional complement. Therefore `3-r ≤ 4-j`, or `r ≥ j-1`.

For completeness, this partial-transversal condition reduces directly to the ordinary independent-transversal induction. Adjoin one new common vector e, outside the three-dimensional dual space, to each of the four groups of coordinate functionals. Every nonempty j-group union now has rank `r+1 ≥ j`. The full independent-transversal lemma gives four independent representatives. Exactly one must be e: two copies are dependent, while four representatives in the original three-dimensional dual space are also dependent. The other three therefore are independent original coordinate functionals from three distinct pairs, as required.

The full lemma itself follows by induction: a proper rank-tight group subset can be solved first, followed by the complementary groups in its quotient; if no proper subset is tight, choose a nonzero representative from the first group and quotient by it, preserving the rank conditions. Thus the coverage argument does not require an unproved stronger rank assertion. Every isotropic three-plane is in at least one of the 32 charts.

## Independent export checks and limits

Using Ryser's subset formula, the reviewer recomputes the full permanent at six deterministic exact assignments of the eighteen lifted parameters. All 31 exported coefficients agree with fixed nonzero rational scaling factors across these assignments. It also checks integer coefficient content, exponent lengths, degree bounds, and parameter order. These are exact sample checks supporting the source review, not a replacement for symbolic polynomial equality in all parameters.

No chart ideal was solved during this review. The original rational chart alone does not cover all isotropic planes; the complete cover requires the stated 32 choices.
