# A rational Witt chart for the full tangent space

This is an exact parameterization and equation export, not a proof or refutation of GCT-231. The first exported chart is only one open chart. A complete family of 32 charts is described below, with its coverage argument independently assessed by finite_cases; that coverage has not been formalized in Lean.

Let H be the standard symmetric 4-by-4 Hadamard matrix divided by two, so H²=I. Every symmetric tangent matrix with total entry sum zero is uniquely

    T = H [0, bᵀ; b, A] H,

with A symmetric 3-by-3. The quadratic coefficient of permanent(J+hT) is

    q(T) = tr(A²) − 6 bᵀb.

Write d=(A11,A22,A33) and o=(A23,A13,A12). The coordinate form is diagonal with weights (1,1,1,2,2,2,−6,−6,−6). In each corresponding coordinate triple (d_i,o_i,b_i), define

    E_i=(2,1,1), F_i=(2,1,−1)/12, R_i=(1,−1,0).

For the bilinear form of q, both E and F are isotropic, EᵀqF=I, and R is orthogonal to them with RᵀqR=3I. These identities and invertibility of the resulting nine-dimensional frame are checked exactly by the generator.

On the open chart where the E-coordinate projection of the proposed three-plane is invertible, normalize it to I. Every isotropic plane then has column matrix

    C = E + F(K − (3/2) ZᵀZ) + RZ,

where K is an arbitrary skew-symmetric 3-by-3 matrix and Z an arbitrary 3-by-3 matrix. This is twelve complex parameters. Conversely this formula is isotropic identically, and any isotropic plane in this open chart has this form.

The exact generator `fresh/witt_hadamard.py` in scratch expands permanent(J+T(x,y,z)) in a rational sparse polynomial ring. It checks that the degree-one and degree-two coefficients vanish identically, then exports all ten cubic and fifteen quartic coefficients. The output is `fresh/witt-hadamard-equations.json`; its parameters are a0,a1,a2 for the upper entries of K, followed by the row-major entries of Z. Each equation is represented by pairs `[integer coefficient string, exponent list]` and is individually made primitive. The cubic equations have 11,224 terms in total; the quartic equations have 102,120. The full log is `fresh/witt_hadamard.log`.

The ten cubic equations together with any subset of quartic equations are necessary. In particular, an engine may first try the three pure quartics indexed by monomials (4,0,0), (0,4,0), (0,0,4), giving thirteen equations. A unit ideal for that smaller set would already exclude this chart. A nonunit ideal for a subset would give no positive witness without checking all remaining equations.

## A complete family of 32 charts

Over Q(i), split the residual R-space into a fourth hyperbolic pair

    E_4=R_1+iR_2, F_4=(R_1−iR_2)/6,

and the anisotropic line R_3 of norm three. Choose three of the four hyperbolic pairs and choose one of the two coordinate functionals from each selected pair as pivots. There are 4·2³=32 choices. The unchosen pair and the anisotropic line form the residual nondegenerate three-space in that chart. The same graph formula holds, replacing 3I by that residual Gram matrix.

To justify coverage, restrict the two coordinate functionals of each hyperbolic pair to a totally isotropic three-plane L. For any set J of j pairs, if their combined restrictions have rank r, their kernel in L has dimension 3−r and lies in the complementary nondegenerate space of dimension 9−2j. Thus

    3−r ≤ floor((9−2j)/2) = 4−j,

so r≥j−1. This is precisely the partial independent-transversal condition for selecting three independent functionals from three distinct groups among the four groups: r+(4−j)≥3 for every J. The standard independent-transversal induction, or Rado's theorem, gives such a choice. Therefore every isotropic three-plane occurs in at least one of the 32 charts. No unit-ideal result for these complete charts is claimed here.

## Numerical candidate search

A separate numerical Witt chart used a floating-point orthogonal diagonalization of q and the same graph construction, so its quadratic coefficient vanished to numerical precision throughout. One thousand bounded complex least-squares starts solved only the cubic and quartic coefficient equations. No root was found; the complete log is `fresh/numeric_witt.log`. This is candidate generation only and supplies no nonexistence conclusion.
