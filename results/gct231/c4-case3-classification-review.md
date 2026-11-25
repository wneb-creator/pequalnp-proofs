# C4 reduced open case 3: independent exact classification review

The original reduced case 3 source has SHA256 `72b12e2f543766e57aec78a88717f5133442553a207566956022363aa89a867f`. Its six equations have exactly the complex solution `(A,beta,U,V,sat)=(4,1/2,0,−12,1/13)`. Both scale lifts of that point violate the separately required square-pencil condition. This conclusion is conditional on the previously reviewed geometric reduction to this open case.

Saturation is exactly `A*beta*det*sat−1=0`, so A, beta and det are nonzero. With `H=beta²+beta−1`, the two supplied identities imply H is nonzero as well: if H=0, the scale equation and A≠0 force 2beta−1=0, contradicting `(2beta+3)(2beta−1)−4H=1`. The leading coefficient of the quadratic scale equation in A is therefore nonzero. Every recorded denominator factors only into nonzero constants, beta and H. Every stripped polynomial divides the known-nonzero product A*beta*H*det.

The independent checker reconstructed every forward and reverse elimination using the linear-root resultant formula and explicit Sylvester determinants, then checked all reductions modulo the scale equation up to recorded nonzero rational content. Thus it did not assume the linear equation's leading coefficient was nonzero; specialization/degree-drop cases are retained as necessary resultant constraints. All norm polynomials and their removed factors were recomputed with exact univariate polynomial arithmetic. The quadratic/linear norm is the resultant `fa*c²−fb*a*c+fc*a²`, valid also when a=0. The combined exact gcd is

`(beta+2)^22 * (2beta−1)^24 / 16777216`.

Consequently beta is −2 or 1/2. The scale equation gives A in {2,3/32} or {4,3/4}, respectively. The endpoint checks use direct equations, with no Gröbner rerun:

- A=2,beta=−2 and A=3/4,beta=1/2 violate saturation directly.
- A=3/32,beta=−2: the linear and quadratic equations force V=0 and U=−86/15; the quadratic equation then equals −4467/640.
- A=4,beta=1/2: the linear equation gives V=−5U−12. The quadratic becomes `−13U(5U+24)/2`; the cubic excludes U=−24/5, leaving U=0,V=−12,sat=1/13.

All original equations vanish at the remaining point. Its two original-scale lifts have alpha=±2, beta=1/2, gamma=±1, u=0, v=∓6. The omitted necessary square condition is −1 at both, excluding this open case.

Independent standalone source/full log: `/tmp/oec/pequalnp-pilot-75/gct231/c4_case3_independent_review.py` and `c4-case3-independent-review.log`, completed 2026-11-25T12:06:40.797707+00:00. The checker records all four data hashes, reconstructs the algebra directly, and has a 180-second cap. It ran no native solver, full-chart Gröbner computation, or Lean compiler. This is an exact scoped case-3 result, not a statement about case 2, the other strata, or the original whole gap.
