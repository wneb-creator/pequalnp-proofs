# Equal-square D boundary in a B-rank-one plane

This note concerns only a boundary of the B-projection-rank-one problem.
The generic B-rank-one problem remains open.

Choose a plane basis (A,K) with B(K)=0 and B(A) nonzero. The target
rank-three setup makes D injective, so D(K) is nonzero. If its three
coordinate squares coincide, they are all nonzero. Scale K to write
D(K)=(1,epsilon1,epsilon2), where each epsilon is ±1. Put
delta=epsilon1*epsilon2. The sign change

    (delta,delta*epsilon1,delta*epsilon2)

has product one, so it is an allowed Hadamard even sign change induced by
a vertex permutation. After this change and scaling K by delta, D(K) is
(1,1,1). Choose a nonzero coordinate of B(A), permute it to coordinate0,
and scale A; trace zero then gives B(A)=(1,tau,−1−tau). Subtract a multiple
of K to arrange D(A)=(0,u,v).

Write R=P−3D. If E1,E2,E3 are the elementary symmetric functions of the
three entries of R(K), the three kernel equations become

    −E1²−6E1+2E2−18=0,
    2E1−E3+6=0,
    E1⁴+4E1³−4E1²E2+8E1²−8E1E2+8E1+4E2²−8E2=0.

Eliminating E2 and E3 leaves 4(2E1+7)(2E1+9)=0. Thus R(K) is an ordered
root triple of one of

    8x³+28x²+37x+8,
    8x³+36x²+45x+24.

Both cubics are irreducible over QQ and have discriminant −167184. For
each branch s=E1, represent the ordered roots as (x,y,s−x−y), with

    x³−s*x²+E2*x−E3=0,
    y²+(x−s)*y+x²−s*x+E2=0.

This six-dimensional field representation covers all six orderings and
all complex embeddings. The three first-variation equations have an
invertible 3×3 matrix in the three entries of R(A), with its exact inverse
recorded in the corresponding linear-elimination JSON. Consequently the
remaining equations are six polynomials in (u,v,tau) over this field.

For native computation use the primitive element a=x+2y. Its minimal
polynomial is the resultant, in x, of the cubic above and

    3x²−2s*x+a²−2s*a+4E2.

The conversion script verifies the resulting degree-six polynomial is
irreducible and gives exact inverse formulas for x and y modulo it.

Current exact result: both E1 branches have native lifted certificates
whose six residual multipliers plus a multiplier of the respective
degree-six field relation combine to 1 over QQ[a,u,v,tau]. Each complete
identity was independently multiplied out from the native output by
`verify_Bone_equal_D_native.py`. The field-map audit additionally substitutes
a=x+2y back into the primitive equations and residuals, verifying both
inverse coordinate formulas and all six original residuals exactly.
These are algebraic certificates, not Lean theorems. A second agent's
independent audit of the complete chain is pending at this checkpoint.

The remaining generic locus can be normalized so that the cubic
first-variation coefficient of tau is nonzero, namely d1²−d3². To justify
this cover: choose an overlapping nonzero B(A) and D(K) coordinate. If
the other two D squares agree but are nonzero and differ from the chosen
square, at least one of their B coordinates is nonzero because sum B=0;
choose that coordinate instead. If both other D coordinates vanish, this
is the already excluded single-support D boundary. The only residual
failure is exactly the equal-square boundary discussed here.
