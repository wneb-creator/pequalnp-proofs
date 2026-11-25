# Complete classification of zero-diagonal solution two-planes

This is a mathematical classification, not yet a Lean theorem. Together with
the previously independently verified nonextension of all 24 listed planes,
it implies that any solution three-plane must have diagonal-coordinate
projection of rank at least two. It does not exclude the remaining ranks.
The UFD classification and all degenerate cases were independently reviewed
and confirmed by fresh_main_proof on 2026-11-25; this is mathematical review,
not a Lean build.

Let a,b,c,d,e,f denote the entries 01,02,03,12,13,23 of a symmetric
zero-diagonal matrix. Put

    p=a+f, q=b+e, r=c+d,
    x=a-f, y=b-e, z=c-d.

The linear permanent condition is p+q+r=0. On that hyperplane the other
coefficients of permanent(J+hT)-24 are

    Q=p²+q²+r²-x²-y²-z²,
    C=pqr-xyz,
    F=Q²/16.

An independent Ryser subset calculation checks these identities in
`gct231/zero_diagonal_classification/verify_formulas.py` and its complete
`verify_formulas-v2.log`. An initial reviewer assertion used an incorrect
factor 1/2 for Q; its failed log is preserved. The corrected exact identities
above leave all zero-set arguments unchanged.

Consider a two-dimensional solution space U. Regard the six coordinates as
linear forms in its polynomial ring C[U], a unique factorization domain.
The coordinate map from U into their six values is injective.

If p and q are independent, then p,q,r=-p-q are nonzero pairwise
nonproportional linear forms. The identity xyz=pqr and unique factorization
force (x,y,z) to be a permutation of (alpha p,beta q,gamma r), with
alpha beta gamma=1. The three binary quadratic forms p²,q²,r² are linearly
independent: the coefficient of pq in r² is two. Consequently Q=0 forces
alpha²=beta²=gamma²=1. Thus U is one of the six permutations times four
sign choices having product one: exactly the 24 known planes. Each is an
actual two-plane because p,q remain free, and the displayed equations
verify that it is a solution.

It remains to exclude dependent p,q. If their span has dimension one, write
(p,q,r)=(a,b,c)h with h nonzero, a+b+c=0, and not all a,b,c zero. If abc is
nonzero, unique factorization of xyz=abc h³ forces x,y,z each to be a scalar
multiple of h. All six coordinate functions would then span at most one
dimension, contradicting injectivity of the coordinate map on U.

If abc=0, the domain identity xyz=0 forces one of x,y,z to vanish identically.
Since a+b+c=0 and not all are zero, exactly one of a,b,c is zero and the other
two are opposites. Hence kappa=a²+b²+c² is nonzero. The remaining two
difference coordinates u,v obey

    u²+v²-kappa h²=0.

The map U to (h,u,v) is injective, but its image would be a totally isotropic
two-space for a nondegenerate three-variable quadratic. This is impossible:
polarization gives U contained in U-perpendicular, whereas that orthogonal
complement has dimension one.

Finally, if p=q=r=0, then xyz=0 again kills one difference coordinate. The
remaining two satisfy u²+v²=0. They give an injective map from U into a
nondegenerate two-variable quadratic space, whose maximal isotropic
dimension is one. This is also impossible. The classification is complete.

For a putative solution three-plane L, the kernel of its diagonal-coordinate
map is its zero-diagonal subspace. Rank zero is already impossible by the
nondegenerate quadratic on the five-dimensional zero-diagonal tangent space.
Rank one would give a zero-diagonal two-plane; the classification identifies
it with one of the 24 planes already checked to admit no third direction.
Therefore the diagonal-coordinate map on L has rank at least two. The tangent
entry-sum equation does not make this map identically zero, and no such
unstated assumption is used.
