Zero-factor boundary coverage for the B-projection-rank-zero case
================================================================

Use the independently verified coordinates r=P_original-2D. The cubic
coefficient on a two-plane is the identity of binary cubic polynomials

    product_i (r_i+D_i) = 2*product_i r_i.

Suppose the product on the right is identically zero. Since C[s,t] is
an integral domain, some r_i is the zero linear form. The left product
then also vanishes, so some r_j+D_j is the zero linear form. Simultaneous
permutation of the three indices leaves the quadratic and quartic
identities unchanged. There are two index orbits.

1. Same index: arrange i=j=0. Then r0=D0=0. Since the D projection has
   rank two, D1,D2 are independent, and a change of the two-plane basis
   makes D=(0,s,t). Write r=(0,a*s+b*t,c*s+d*t). This is the `same` chart.

2. Different indices: arrange i=0,j=1. Then r0=0 and r1=-D1. Since D
   has rank two, at least one pair of its coordinate forms is independent.
   Normalize that pair to (s,t). The three resulting charts are exactly

       different01: D=(s,t,c*s+d*t), r=(0,-t,a*s+b*t);
       different02: D=(s,c*s+d*t,t), r=(0,-c*s-d*t,a*s+b*t);
       different12: D=(c*s+d*t,s,t), r=(0,-s,a*s+b*t).

No independence is assumed for an unselected pair, so these three charts
include all dependent-D subcases. Multiple zero factors are also included.

In all four charts the cubic is identically zero. The eight necessary
equations are the three quadratic coefficients and five coefficients of
P_mod_q. The exact identity

    P = P_mod_q + q^2/16 + q*(dot(D,r)/2+dot(D,D)/4)

shows that replacing the quartic by P_mod_q is valid once q is the zero
binary polynomial. The compact six-variable identities were independently
expanded in `trace-Bzero-compact-identities.json`.

The four normalized systems each have explicit rational-polynomial
certificates with nonzero constant targets. Their sums were independently
multiplied in QQ[a,b,c,d]:

    same:        target 14120524, 29 multiplier monomials;
    different01: target 8626,     79 multiplier monomials;
    different02: target 887,      63 multiplier monomials;
    different12: target 210,      63 multiplier monomials.

Inputs and multipliers are in `Bzero-boundary-certificates-verified.json`.
Each source system was additionally checked against direct 24-term
permanent coefficients on three exact rational parameter assignments.
The complete native stdout/stderr and verifier sources are retained.

This closes the zero-factor boundary of the B=0, D-rank-two case. The
nonzero-factor UFD charts are supplied separately by geometry_search.
This document is a mathematical coverage argument, not a Lean proof.
