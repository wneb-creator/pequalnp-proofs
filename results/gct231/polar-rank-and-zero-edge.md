# Polar rank and the zero-edge pencil chart

These are exact symbolic mathematical checks, not Lean-checked statements. They do not settle L-gct-231.

For a constant-permanent pencil spanned by symmetric matrices A and B, the coefficient of z in permanent(J+xA+yB+zC) gives ten linear functionals of C. Their common kernel contains A and B. Any three-dimensional constant-permanent extension must therefore make this polar matrix have rank at most seven. This is only a necessary condition.

There is an exact counterexample to the stronger inference that polar rank at most seven forces transposition stability, even for a pencil whose diagonal projection has rank one. Put r=√2. Let B have B00=−1−r, B03=B30=1, B33=−1+r and all other entries zero. Let A have A01=A10=A13=A31=1, A12=A21=−2 and all other entries zero. Then permanent(J+xA+yB)=24, the polar matrix has rank six, and none of the six vertex transpositions preserves span(A,B). Agent `/root/fresh_main_proof/c3_review` independently checked these facts using Ryser's permanent formula, completing at 2026-11-25 11:00:19 UTC. Source and full log: scratch `fresh/polar_rank/rank_checks.py` and `.log`.

Nevertheless this particular pencil cannot extend. After subtracting a combination of A and B, normalize C01=C03=0. The first variation leaves only C12 and C33. The exact residual ideal over Q(√2) has a Groebner basis containing

    C12² − (6+3√2) C12 C33 − (189/2+63√2) C33²,
    C33³.

Thus C33=0 and then C12=0. The independent computation additionally verifies membership of C12⁴ and C33³, and checks both projective charts. Source/full log: scratch `fresh/polar_rank/triple_star_extend.py` and `.log`; completion 2026-11-25 11:01:21 UTC. This separates failure of the symmetry inference from existence of a three-dimensional extension.

For the separate zero-edge pencil chart, set T03=0, T01=x, T02=y, leave the other three offdiagonal entries and the first three diagonal entries as arbitrary linear forms in x,y, and eliminate T33 by the tangent equation. This gives twelve scalar variables and twelve coefficient equations: three quadratic, four cubic, five quartic. Their expanded total is 731 monomials. The two known zero-diagonal planes in this chart both have coefficient-Jacobian rank nine, hence Zariski tangent dimension three. This does not prove positive local dimension, since an isolated nonreduced point can have a larger tangent space. It shows that the naive equal-equation-count heuristic is insufficient to assert isolated reduced solutions.

The two zero-diagonal seeds have offdiagonal entries (01,02,03,12,13,23) respectively

    (x,y,0,−2x,x,−y),
    (x,y,0,−2y,−x,y).

Exact generator and full output: scratch `fresh/zero_edge_pencil.py` and `.log`; deterministic equation export `fresh/zero-edge-pencil.json`. No Groebner computation was run for this twelve-variable chart.
