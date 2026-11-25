# Fixed-C4 quadratic/cubic factor route

This is scoped to symmetric matrices with entries 02 and 13 zero. It is not a proof or refutation of the whole gap. Exact polynomial checks and small elimination systems are in scratch; independent review of the open-case elimination is pending.

Write the four remaining off-diagonal entries as x=t01, y=t12, z=t23, w=t03 and the diagonal entries as d0,d1,d2,d3. The linear coefficient of per(J+s t) vanishes precisely when the total entry sum vanishes, so impose d0+d1+d2+d3=-2(x+y+z+w). Define seven rational linear coordinates:

- e=x+y+z+w and f=x+z-y-w;
- a=2(d1-d3), b=2(d0-d2), H=d0+d2-d1-d3;
- X=2(x-z)+(d0-d2)+(d1-d3);
- Y=2(y-w)-(d0-d2)+(d1-d3).

The quadratic coefficient, multiplied by 4, is

    q = 6e² + 2f² + a² + b² - H² - X² - Y² - X(a+b) + Y(b-a).

The cubic coefficient, multiplied by 16, is

    c = 2fab - 2HXY
        + e[-4X²-4Y²+4X(a+b)+4Y(a-b)-a²-b²+4f²] - 4e³.

The exact substitution assertions in `c4_factor_coordinates.py` check both formulas against the direct 24-permutation permanent expansion. An earlier informal cross-factor expression was incorrect and was corrected before use; only the formulas above are used in the subsequent systems.

If a candidate three-plane L has q=c=0, its intersection K with e=0 has dimension at least two. On K, the cubic condition is the product identity fab=HXY. This gives two cases.

If a factor vanishes identically, one factor on each side vanishes. Fresh's separate work treats the nine coordinate-pair cases and the possibility that all of L lies in e=0.

If no factor vanishes, unique factorization in the polynomial ring on K pairs H,X,Y with a permutation of f,a,b, with nonzero scales alpha,beta,gamma satisfying alpha*beta*gamma=1. The restrictions f,a,b span two dimensions: if they spanned only one, all six factor coordinates would do so, contradicting the injective coordinate map on the two-plane K. Thus either f,a are independent or a,b are independent. The direct export `c4_nonzero_branches.json` records all twelve extension charts and makes no branch-exclusion claim.

A smaller approach places K inside a four-space W defined by two proportionalities. On the open set where q restricted to W is nondegenerate, subtracting a K component normalizes an extension vector to W's orthogonal complement. Fresh exported necessary equations in three scales and two extension parameters. For permutations 0 and 1, substituting alpha=1/(beta*gamma), removing only factors known nonzero from det(q|W), and eliminating the extension parameter u by resultants gives four bivariate necessary equations in each of the cases v=0 and v nonzero. No leading coefficient of a resultant is divided out.

Exact QQ Groebner computations on the squarefree necessary equations give unit ideals for v=0. For v nonzero, case 0 forces (beta+gamma)²=0 and (gamma²-gamma-1)²=0; case 1 forces (beta-gamma)²=0 and (gamma²+gamma-1)²=0. Either implies beta²+beta-1=0, which is excluded on these open sets. These are CAS findings pending independent review and certificate conversion. Degenerate four-space boundaries and permutations 2 through 5 are separate obligations handled by Fresh's branch.
