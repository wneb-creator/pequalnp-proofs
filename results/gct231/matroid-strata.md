# Conditional offdiagonal matroid strata

This reduction is conditional on excluding planes with independent star and triangle offdiagonal coordinate triples. No such full-chart exclusion is asserted here. The determinant calculation and the two-block deduction were independently checked by finite_cases. The remaining C4-support chart parameterization has independent review in `c4-support-review.md`; no chart has yet been solved.

Choose an independent path triple and use e01=X, e12=Y, e23=Z as coordinates on a candidate three-plane. Write the other offdiagonal coordinate vectors as e02=A, e03=B, e13=C. Vanishing of all four star and all four triangle minors forces

    A=aY, C=cY, B=b1 X+b2 Y+b3 Z,
    a b1=a b3=c b1=c b3=0.

Over a field there are exactly two resulting linear strata: either b1=b3=0, or a=c=0. The independent exact determinant log is scratch `gct231/matroid-strata-review.log`.

## The central stratum reduces to the nonextendable block seed

When b1=b3=0, set y=0. The resulting two-plane is block diagonal on vertex pairs {0,1} and {2,3}, with offdiagonal entries x and z respectively. Let sA,sB be the block entry sums and pA,pB the two-by-two block permanents. The four homogeneous coefficients of permanent(J+T)−24 are

    6(sA+sB), 2(pA+pB+sAsB), sA pB+sB pA, pA pB.

In the polynomial ring on x,z, these imply sA=sB=pA=pB=0. Indeed pApB=0, and after sB=−sA the other equations give pA+pB=sA² and sA(pB−pA)=0; domain cancellation forces sA=0, then both pA and pB vanish.

For the first block write d0=αx+βz and d1=−2x−d0. The z² coefficient of its permanent is −β², so β=0. Its x² coefficient yields α²+2α−1=0. The second block is analogous. Hence this is exactly diag(xA±,zA±), where A± has offdiagonal one and diagonal (−1±√2,−1∓√2). Swapping the two vertices within either block swaps its sign. The independently reviewed arbitrary-third-direction block-seed obstruction therefore excludes this entire stratum.

## The remaining stratum has fixed C4 support

When a=c=0, the entries T02 and T13 vanish identically. All symmetric tangent matrices with these two zero entries form a seven-dimensional space. The quadratic permanent coefficient has Gram determinant −1728 and is nondegenerate, so a solution three-plane is a maximal totally isotropic subspace of this quadratic space.

In Hadamard coordinates T=H[0,bᵀ;b,A]H with H the normalized Hadamard matrix, the support constraints are d2=d1+d3 and b2=o2. Put u=d1+d3 and v=d1−d3. Then the quadratic is

    (3/2)u²+(1/2)v²+2o1²−4o2²+2o3²−6b1²−6b3².

A rational Witt frame is given in coordinate order (u,v,o1,o2,o3,b1,b3) by

    E1=(2,0,0,0,0,1,0), F1=(2,0,0,0,0,−1,0)/12,
    E2=(0,0,1,1,1,0,0), F2=(0,0,1,−1,1,0,0)/8,
    E3=(0,2,1,0,−1,0,1), F3=(0,2,1,0,−1,0,−1)/12,
    R =(0,4,−1,0,1,0,0).

The E/F mutual Gram matrix is I3 and R has norm12. In any of the eight choices of one pivot coordinate from each hyperbolic pair, an isotropic three-plane is

    E X + F(K−6rᵀr)X + R(rX),

with K skew-symmetric and r a row of length three. This gives six parameters over Q. The odd-dimensional independent-transversal argument covers all maximal isotropic three-planes: projection to any j pair groups has rank at least j because its kernel is isotropic in a complementary (7−2j)-dimensional nondegenerate space. Thus one independent functional can be selected from each pair.

The exact generator is scratch `fresh/c4_support_rational_charts.py`, using `c4_support_charts.py` for the worker and `c4-support-homogeneous.json` for the original homogeneous polynomials. The first output is `c4-support-rational-chart-0.json`, with25 cubic/quartic coefficient equations in six variables. It has5609 total terms and degrees6 and8. A120-second SymPy attempt returned UNKNOWN_TIME_LIMIT. This is not a nonexistence result. Native sparse-engine testing is coordinated by root and finite_cases.

## Lower-degree equation exports

The exact substitutions into the previously reviewed offdiagonal full-chart equations also produce:

- `fresh/path-central-equations.json`:12 variables,31 equations,1039 terms;
- `fresh/path-c4-equations.json`:12 variables,31 equations,973 terms;
- `fresh/triangle-star-dependent-equations.json`:15 variables,32 equations,1470 terms.

All these systems have degree at most four. The last one sets the three star-forced zero coefficients in the triangle chart and adds the remaining star determinant. The source and complete generation log are `fresh/matroid_strata.py/.log`. These are conditional strata, not replacements for proving the antecedent full-chart exclusions.
