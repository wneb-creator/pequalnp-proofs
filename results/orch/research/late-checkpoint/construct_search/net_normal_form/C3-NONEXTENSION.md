# C3-stable trace-zero planes: arbitrary nonextension

Research proposition: let L be a two-dimensional complex subspace of symmetric 4 by 4 matrices, stable under the vertex cycle (1 2 3), with trace zero on L, diagonal projection of rank two, and permanent(J+T)=24 for all T in L. Then any matrix W satisfying the first-order permanent compatibility conditions along J+L belongs to L. In particular L has no three-dimensional constant-permanent linear extension. This is supported by exact polynomial certificates and independent audits below; it is not yet formalized in Lean.

## Exhaustive normalization

Write w for a primitive cube root of unity. The cycle acts diagonally with eigenvalues1,w,w². A trace-zero trivial-character direction has diagonal(-3r,r,r,r), all three off-diagonal entries incident to vertex0 equal t, and the other three equal -t. Its quadratic and cubic coefficients are

q=-12(r²-4rt+t²), c=-8(r³-3r²t+3rt²+t³).

For t=0 the quadratic forces r=0. For t≠0, set x=r/t. The exact identity

(-x²/72+x/24-1/36)q(x,1)+(x/48-1/12)c(x,1)=1

excludes a nonzero valid trivial-character direction. A two-plane within either remaining single character has diagonal rank at most one. Thus L has one w direction and one w² direction, both with nonzero diagonal coefficients.

Their coefficients on the three entries incident to vertex0 must both be nonzero. If exactly one vanishes, normalize its diagonal to1. Its cubic and the mixed quartic give

f(x)=1+3x²+2x³=0, g(x)=1+2x+3x²=0,

contradicted by (x+11/12)f+(-2x²/3-7x/6+1/12)g=1. If both incident coefficients vanish, normalize both diagonals to1. The quadratic gives y=1/2-x, and the two cubics f(x)=f(y)=0 contradict

(8x²/13-22x/13+31/39)f(x)+(8x²/13+14x/13+4/39)f(1/2-x)=1.

Consequently both incident coefficients can be normalized to1, giving the following exhaustive chart:

U=[[0,1,w²,w],[1,a,wB,w²B],[w²,wB,w²a,B],[w,w²B,B,wa]],
V=[[0,1,w,w²],[1,c,w²D,wD],[w,w²D,wc,D],[w²,wD,D,w²c]],

with a*c nonzero. The four nonconstant permanent coefficients, up to factors6,1,1,3, are

q=-ac+2aD+2Bc-2a-2c+2B+2D,
C(a,B)=a³+6a²+3aB²-6aB+3a+2B³+6B,
C(c,D),
P=(a-c)²+2(a-c)(B-D)+3(B+D)².

The failed exploratory rational parametrization in c3_parametrize.py used the wrong sign in factoring C. Its degree20 output is INVALID and is excluded from the evidence manifest.

## Arbitrary first-order extensions

The full10-dimensional space of symmetric matrices decomposes into character dimensions4,3,3. The derivative of the permanent along J+xU+yV gives four equations on the trivial part and three equations on each other part. All34 block entries, all omitted coefficients, and invertibility of the10-vector character basis were independently checked by root's sixteen-subset Ryser expansion. No symmetry is assumed for W.

The blocks are recorded in c3-extension-blocks.json. After eliminating the trivial part's tangent equation and adding multiples of q,C(a,B),C(c,D), its remaining3 by3 matrix is N. Put r=a-B, s=c-D, K=BD-aD-Bc-2B-2D+1. Then

N=[[K-3(r+s), -6(r+s), -7(r+s)-K],
   [6ar+2a+8B, 14ar+6a+12B, 12ar+8a+12B],
   [6cs+2c+8D, 14cs+6c+12D, 12cs+8c+12D]].

The row reductions were independently verified as exact polynomial identities. The plus-character block has a2 by2 minor equal to -36m, where

m=-6BD+5Bc+8B-6D²-2Da+3Dc+4D+3ac+4a-3c²-4c.

The minus-character block is obtained by simultaneously swapping(a,B) with(c,D).

## Explicit certificates and independent verification

1. c3-certificate-trivial.stdout records six explicit polynomial multipliers proving1 is in the ideal(q,C(a,B),C(c,D),P,zac-1,detN). There are2020 multiplier terms; z is an auxiliary inverse of ac.
2. c3-power-certificate-plus.stdout records five explicit polynomial multipliers proving ac is in the ideal(q,C(a,B),C(c,D),P,m). There are467 multiplier terms. Thus m cannot vanish when ac is nonzero. The swapped certificate treats the minus block.

The standalone audit_c3_certificates.py parses every rational coefficient, clears one common denominator, multiplies integer-polynomial dictionaries, and checks both identities exactly. It also verifies every row reduction defining N. This audit does not invoke a Groebner-basis engine. c3-certificates-independent-audit.json records PASS and the certificate hashes. audit_c3_boundaries.py independently verifies the three small Bezout identities and the variable-swap symmetry.

It follows that the trivial block has rank4 and the two other blocks have rank2. Their kernels already contain U and V respectively, so those kernels are precisely their one-dimensional spans. The full compatibility kernel is therefore L.

## Scope and preservation

The result covers every C3-stable, trace-zero two-plane with diagonal projection of rank two, including every projective boundary. It does not classify all trace-zero two-planes and does not settle L-gct-231.

The exact certificate sources, complete outputs, audits, and root's independent Ryser checks are listed with hashes in c3-valid-evidence-manifest.json. A simplification attempt found no degree6–9 Macaulay representation of the smaller target(ac)²; degree10 hit its address-space cap. A separate oversized power-certificate export hit its output cap and is not used. No incomplete or invalid certificate is included as supporting evidence.
