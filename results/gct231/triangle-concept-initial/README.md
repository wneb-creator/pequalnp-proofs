# Triangle chart with all four stars dependent

This is a conditional reduction of the triangle chart, not a proof or refutation of L-gct-231. The original chart has pivots T01=x, T02=y, T12=z and

    T03=a*x+b*y, T13=c*x+d*z, T23=e*y+f*z,
    a*d*e+b*c*f=0.

The other variables d0,...,d8 are the coefficients of the first three diagonal entries as in `fresh/triangle-star-dependent-equations.json`. Here a,b,c,d,e,f correspond to o0,o1,o3,o5,o7,o8.

## Three forced diagonal zeros

For a direction with one isolated vertex, write its diagonal as δ and its remaining symmetric 3×3 block's entry sum, second rook sum and permanent as s,r,p. The coefficients of permanent(J+tT)−24 are

    L=6(s+δ), Q=2(r+sδ), C=p+δr, F=δp.

The exact identity

    δ⁴ = δ³L/6 − δ²Q/2 + δC − F

forces δ=0 on a constant-permanent line. The arbitrary-vertex result has now been Lean checked separately in `isolated-vertex/IsolatedVertex.lean`; independent source review is recorded in `isolated_vertex_review/`.

The x direction isolates vertex 2, the y direction isolates vertex 1, and the z direction isolates vertex 0. Therefore

    d6=d4=d2=0.

The raw chart's built-in tangent equation makes L=0 already. The three corresponding identities δ⁴+F−δC+δ²Q/2=0 were checked directly against its exact polynomial coefficients.

## Center diagonal relations without genericity assumptions

For every vector in the kernel of a vertex's star map, the same isolated-vertex lemma makes that vertex's diagonal vanish. Hence its diagonal functional lies in the span of its incident off-diagonal functionals. This argument applies even when the star rank is zero or one.

For vertex 3 put

    M = [[a,b,0],[c,0,d],[0,e,f]],
    t = [d0+d3+2, d1+d7+2, d5+d8+2].

After the three forced diagonal zeros, the coefficient row of T33 equals −t minus twice the sum of M's rows. Thus t lies in the row span of M. Since det(M)=0, the determinant made from any two rows of M and t must vanish. The export appends exactly these three minors. For example, the first is

    b*d*(d0+d3+2) − a*d*(d1+d7+2) − b*c*(d5+d8+2) = 0.

No division by an off-diagonal parameter is used.

## Smaller exact export

The three pure quartic coefficients vanish identically after d2=d4=d6=0. Each of the six quartics with an exponent 3 is exactly a diagonal coefficient times a pure cubic coefficient; for example, [x³y]F=d7[x³]C and [x³z]F=d8[x³]C. They are redundant once the cubic equations vanish.

`triangle_concept/triangle-twelve-equations.json` therefore has twelve variables, 26 equations and 686 expanded terms: six quadratics, ten cubics, six remaining quartics, the original star determinant, and three center-diagonal minors. Its SHA256 is 03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7. Independent review recomputed every original coefficient with Ryser's formula and checked every exported equation and minor. This is a necessary system; no inconsistency verdict is asserted here.

## A fourth double point further simplifies the quartic on an open set

At a matrix whose row and column i vanish, the derivative of its permanent in direction W is Wii times the permanent of the complementary 3×3 block. The cubic coefficient C at that matrix is precisely that complementary permanent. Thus C=0 makes every isolated parameter point a double point of the quartic F.

The three axis points explain the redundant quartics above. If the center-star kernel has three nonzero coordinates, rescale parameters to put its isolated point at (1,1,1). Write the six surviving quartic coefficients as

    F=A*x²y²+B*x²z²+C*y²z²+D*x²yz+E*xy²z+G*xyz².

The three derivative equations at (1,1,1) have coefficient determinant 4 and give

    D=C−A−B, E=B−A−C, G=A−B−C.

Equivalently F=B q1²+C q2²+(A−B−C)q1q2 for q1=x(y−z), q2=y(x−z). Only the three pair-square coefficients need be imposed on that open set. The separate `triangle-twelve-relaxed23-equations.json` drops the other three quartics; it is a weaker necessary system everywhere, and the omitted quartics follow under the stated nonzero-coordinate hypothesis. No claim about this open condition on every candidate is made.

## A small obstruction for center-star rank at most one

For symmetric 3×3 constant-permanent pencils, consider a pencil containing a coordinate-edge direction. Off-diagonal projection is injective, so after subtracting a multiple of that direction and normalizing, its matrix can be written

    [[p*x, x, k*x],
     [x, r*x+s*y, y],
     [k*x, y, −(p+r+2+2k)*x−(s+2)*y]].

The zero y coefficient of the first diagonal follows from the 3×3 isolated-vertex analogue: L=2(s_block+δ), Q=p_block+s_block*δ, C=δ*p_block give δ³=C−δQ+δ²L/2. The pure-y quadratic then gives s²+2s−1=0. The mixed quadratic solves

    r=−p/2−2+(s+1)*(2k+p+2)/4.

Its divisor −2(s+1) is nonzero because (s+1)²=2. Substitution and exact reduction modulo s²+2s−1 leave four rational equations in p,k,s, totaling 34 terms. Their exact QQ Gröbner basis is [1], computed in 0.018 seconds. Both conjugate two-variable calculations over Q(√2) also give [1]. These are exact CAS diagnostics pending independent transformation review and certificate/Lean conversion, not yet a Lean theorem.

If the triangle chart's center star has rank one, its kernel is a two-plane. The center diagonal also vanishes there, yielding a symmetric 3×3 constant-permanent pencil. The common star linear form has at least one zero coefficient, since each nonzero row of M does, so this pencil contains a coordinate-edge direction. The small obstruction therefore applies once certified and its chart bridge is supplied. Rank zero is the already excluded triangle-support three-plane. The general center-star rank-two case remains open.

For calibration, the easier 3×3 path pencil with one identically missing edge gives a unit ideal in 0.016 seconds. A ten-second, 512-MiB exact diagnostic for the full six-variable 3×3 two-plane chart timed out and remains UNKNOWN; it supplies no general 3×3 exclusion.

## A tested limit of the row-rank argument

The geometric row-rank conditions alone force neither a common kernel nor a permutation-stable subspace. Set all diagonal coefficients to zero and

    (a,b,c,d,e,f)=(2,3,−3,−9,−4,8).

Every full row map has rank two, the tangent entry sum is zero, and the star determinant vanishes. Yet the matrix at (1,1,1) has determinant 361, so the space has no common kernel. Exact checks of all 24 vertex permutations find only the identity in its stabilizer. Its quadratic coefficient is −4(7xy−10xz+6yz), so it is not a constant-permanent candidate. This counterexample only rules out using the weaker geometric premises alone to infer either proposed structure.

All generators, complete diagnostics, exact exports and independent review logs are in scratch `gct231/triangle_concept/`. No large CAS run was launched for this conceptual route; the only timed-out diagnostic had an explicit ten-second cap.
