# Exact and numerical family searches for L-gct-231

No three-dimensional witness or full refutation has been found. Every numerical or timed-out search below is explicitly inconclusive. Sources, complete logs, equation data, and a hash manifest are in `finite/`.

## Exact symbolic obstructions

For perturbations supported in two rows/columns, write t=[[a,b,x,y],[b,c,z,w],[x,z,0,0],[y,w,0,0]]. Its quartic permanent coefficient is (xw+yz)^2. The cross block of any linear constant-permanent family is therefore a linear space in a smooth determinant quadric, of dimension at most two. For the ruling B=[[u,v],[ku,−kv]], the cubic coefficient is a k^2(u−v)^2+2bk(u^2−v^2)+c(u+v)^2. For the other ruling B=[[u,ku],[v,−kv]], it is a(1−k)^2v^2+2b(1−k^2)uv+c(1+k)^2u^2. Coefficients of any A-only kernel direction, together with tangent a+2b+c=0 and A-only quadratic ac+b^2=0, force that direction to vanish. If the cross-block image has dimension at most one, the A-only kernel would have dimension at least two, impossible for its tangent conic. This is a mathematical subclass argument using the usual two-ruling classification; no Lean proof of it is claimed. Exact expansions for both rulings are saved.

The fixed-u rank-two ansatz t=uv^T+vu^T, with sum u=0, u·u=0 and v in u-perp, also fails. Taking v=u forces some u coordinate zero from the quartic term. Up to scaling/permutation, u=(1,omega,omega^2,0), omega^2+omega+1=0. For v=A(1,1,1,0)+Bu+Ce3, exact reduction gives permanent(J+zt)−24=12z^3(A^3+3A^2C+4B^3)+72z^4 B^2 C^2. Thus the cubic already obstructs this full three-parameter ansatz.

A six-dimensional Hadamard matching ansatz has off-diagonal coordinates (x,y,z,−z,−y,−x) and diagonal (d+e+f,d−e−f,−d+e−f,−d−e+f). Its quadratic coefficient is −4(d^2+4dx+e^2+4ey+f^2+4fz+x^2+y^2+z^2); its cubic coefficient is 8((d+x)(e+y)(f+z)−2xyz). The 48 signed-permutation orthogonal graph choices all fail the cubic. Full symbolic quadratic/cubic/quartic expansions are saved. This finite scan is not a global classification.

## Normalized chart calculations

The shared generator fixes three off-diagonal pivot entries as x,y,z. In full mode, the other three off-diagonals and the first three diagonals are arbitrary linear forms (18 coefficient unknowns); diagonal33 is minus the sum of the other diagonals minus twice the off-diagonal sum. This enforces the first permanent derivative. Equating all remaining parameter monomials gives six quadratic, ten cubic, and fifteen quartic equations. Independent review by /root/library_route reconstructed both star-support and full-star equations using Ryser inclusion-exclusion and checked 24 exact integer samples against direct permutations. Equation generation passed; Groebner certificates were not certified by that review.

The star coordinate-support subcase, where other off-diagonals are zero, has nine unknowns. Exact QQ Buchberger computation returned the unit Groebner basis [1] in 87.63 seconds. The preceding F5B run hit its 180-second cap. This is an exact CAS result for the subclass, but no ideal-membership certificate has yet been translated into Lean. Full-star QQ Buchberger reached its 300-second cap without a basis or verdict.

Full-star complex least-squares used 1000 random starts with fixed pivots and an analytic Jacobian. The best infinity-norm residual was approximately 0.04692456, so there is no candidate to reconstruct exactly. No nonexistence inference follows.

Full-star modular Macaulay tests modulo 1009 found no unit certificate through degree four or five. Degree four: 1345 rows, rank 1330, 7315 columns. Degree five: 10165 rows, rank 9820, 33649 columns. These are only finite-field, bounded-degree row-space calculations; they do not establish any characteristic-zero conclusion.

A separate direct GMP-rational OpenF4 adapter compiled and passed unit, nonunit, and rational-coefficient toy controls. Its known star-support nine-variable test reached the 120-second cap under a 2 GiB address-space limit; this supplies no verdict. Sources, signed-integer converter, bounded runner, toy inputs/logs, and the complete timed-out run are preserved here. No full chart was run in this rational engine. Structural is exploring an isolated row-operation trace overlay. No named proof file, desk, git, or PR action was performed by this finite-search agent.


## Further exact bounded searches and modular engine diagnostics

Exhaustive integer entry boxes [-1,1], [-2,2], and [-3,3] were searched after eliminating the last diagonal entry using the tangent equation. Up to sign and primitive scaling, they contain respectively 12, 120, and 168 constant-permanent line directions. The compatible pairs represent respectively 1, 3, and 3 plane orbits under simultaneous S4 permutation. None contain an independent pairwise-compatible triple. The three plane orbits coincide with cases already excluded by fresh_main_proof. These finite searches do not classify arbitrary complex families.

The Gaussian unit set {0,1,−1,I,−I} was also searched completely: 1,953,125 trace-determined inputs represent all 5^10 entry patterns. It contains 30 constant-line directions up to multiplication by a unit, 12 compatible pairs, and no independent pairwise-compatible triple. Computation uses paired int64 arrays with exact Gaussian integer addition/multiplication, not floating point. All degree-at-most-four expressions are far below overflow. Pair compatibility is checked at A+B, A−B, A+2B after the endpoints are already constant lines; polynomial degree bounds make this sufficient. For a pairwise-compatible independent triple, only one cubic and three quartic fully mixed coefficients remain; three signed sum evaluations check them.

An isolated OpenF4 copy caps selected critical pairs per batch at 32. The known star-support unit control returns [1] modulo 1009 in 0.066 seconds. The full-star modular trial aborts with std::bad_alloc after 28.04 seconds under a 4 GiB address-space limit. Its last logged stage is degree six, 485 basis polynomials, 3767 queued pairs, and a matrix of 8722 rows by 39880 columns with 8689 pivots. This is UNKNOWN with no algebraic verdict. The complete log, exact input provenance, minimal one-line engine patch, and driver source are preserved; no binary is committed. A proposed old-matrix reset was inspected by structural_proof but was not part of this trial.
