# GCT-231 fresh algebraic investigation

Exact target: a three-dimensional complex linear subspace of symmetric 4-by-4 perturbations t with permanent(J+t)=24 identically. No proof or refutation of the full statement has been obtained. All computations below are exact symbolic mathematical evidence unless explicitly marked numerical; none has yet been translated into Lean.

## Standard star plane cannot extend

Let T(x,y) have first row/column (0,x,y,-x-y) and all other entries zero. This is a two-dimensional constant-permanent plane. For a symmetric candidate B, requiring the coefficient of z in permanent(J+T(x,y)+zB)-24 to vanish identically forces the lower-right 3-by-3 block of B to be constant c and B00=-2S-9c, where S=B01+B02+B03. The remaining coefficients include

- z²: 2(S²-6Sc-63c²),
- z³: 4c(S²-6Sc-39c²).

Subtracting c times the first reduced equation from the second reduced equation gives 24c³=0. Over the complex numbers c=0, then S²=0 forces S=0. Hence B already lies in the original star plane. Script: scratch gct231/fresh/star_extend.py.

## Rank-two fixed-vector ansatz cannot work

For t=u vᵀ+v uᵀ with sum u=0, u·u=0, v·u=0, the linear and quadratic permanent coefficients vanish. However the three-dimensional parameter space u-perpendicular contains v=u, hence contains the nonzero symmetric rank-one direction 2uuᵀ. No nonzero symmetric rank-one direction is constant-permanent: permanent(J+a uuᵀ)=sum_{k=0}^4 k!(4-k)! e_k(u)^2 a^k. Constancy forces all e_k(u)=0, so all coordinates of u are zero. Thus this full three-dimensional ansatz is impossible.

## Sparse block obstructions

For a fixed 2+2 symmetric block-diagonal perturbation, let sA,sB be the sums of the entries of the two blocks, and pA,pB their permanents. The homogeneous equations force sB=-sA, pA+pB=sA², sA(pB-pA)=0 and pApB=0. In the polynomial ring on the proposed linear space, this implies sA=sB=pA=pB=0. Each symmetric 2-by-2 block with these conditions contributes at most one linear dimension, so the total dimension is at most two.

The triangle-coordinate-support case is a 3+1 block decomposition t=diag(A,d), with A symmetric 3-by-3. Write s for its entry sum, r for its degree-two rook sum and p for its permanent. The four homogeneous equations force d=-s, r=s², p=s³ and dp=0, hence s=d=r=p=0. The second-rook quadratic on symmetric 3-by-3 matrices with entry sum zero is nondegenerate on a five-dimensional space, so its totally isotropic subspaces have dimension at most two. This rules out three-dimensional families supported on one offdiagonal triangle, even with arbitrary diagonal linear forms.

## Twenty-four zero-diagonal planes and extension checks

Write the six offdiagonal entries as a=t01,b=t02,c=t03,d=t12,e=t13,f=t23. Let opposite-edge sums p=a+f,q=b+e,r=c+d and differences x=a-f,y=b-e,z=c-d. With p+q+r=0, the homogeneous conditions reduce to

    x²+y²+z²=p²+q²+r²,
    xyz=pqr.

The quartic coefficient is the square of the quadratic expression divided by sixteen and gives no further condition. Any signed permutation (x,y,z) of (p,q,r), with product of the signs equal to one, therefore defines a constant-permanent two-dimensional plane. The script planes_extend.py checks all twenty-four distinct such planes. In every case, the linear variation equations for a third direction followed by the remaining coefficients force that direction back into the original plane. Some cases reduce to the star obstruction above; the three-cycle permutation cases reduce directly to a residual coefficient -16c². The full exact output is planes_extend.log. This is not a classification of all zero-diagonal two-planes.

A zero-diagonal three-plane is impossible already from the quadratic coefficient: after the total-entry-sum equation, the offdiagonal tangent space is five-dimensional with nondegenerate quadratic form, so maximal isotropic dimension is two.

## Full triangle chart

The offdiagonal projection of any putative three-plane is injective: a nonzero diagonal direction cannot have constant permanent, since its four elementary symmetric polynomials would all vanish. Thus three offdiagonal entries can be chosen as coordinates. Up to vertex permutations the pivot patterns have three graph types: star, triangle, and path. Finite_cases coordinates the common exact generator; this agent owns triangle.

The full triangle chart uses t01=x,t02=y,t12=z, permits arbitrary linear forms for the other three offdiagonal entries and the first three diagonal entries, and eliminates t33 by the degree-one equation. There are eighteen complex unknowns and thirty-one homogeneous coefficient equations. A bounded exact Groebner computation and an independent numerical complex least-squares candidate search are running. Numerical residuals alone will not be treated as a proof of nonexistence or as an exact construction.

## Completed full triangle searches

The exact full triangle Groebner run reached its native 300-second limit with `UNKNOWN_TIME_LIMIT`; no basis or nonexistence verdict was returned. The simpler triangle-support Groebner run also timed out at 180 seconds, although the independent 3+1 block/Hessian argument above handles that restricted case.

Numerical candidate generation completed 100 initial complex random starts, 1,000 additional starts at scales 0.01, 0.1, 1, 3, 10 and 30, and 200 staged runs which first solved the quadratic/cubic conditions and then increased the quartic weight through 0.01, 0.1 and 1. No root was found. The best maximum coefficient residual in the 1,000-start run was approximately 0.103411568, at coefficient norm approximately 4.4158. These are failed searches, not nonexistence evidence. Scripts and full logs are numeric_triangle*.py/log in scratch gct231/fresh.

## Three-cycle-stable planes are excluded

This is a scoped exact symbolic argument, not a general classification and not Lean checked.

Let a 3-cycle permute vertices 1,2,3 and fix vertex 0. Its invariant tangent matrices have diagonal (a,c,c,c), entries b from vertex 0 to the other vertices, and entries d between the last three vertices. The linear condition gives a=-6b-3c-6d. The remaining coefficients are

    -6*(-3b²+2bc+4bd+2c²+10cd+9d²),
    -4*(-3b²c-6b²d+3bc²+6bcd+9bd²+2c³+9c²d+15cd²+13d³),
    -3*(-b²c²-2b²cd-3b²d²+2bc³+6bcd²+4bd³+c⁴+2c³d+3c²d²+8cd³+4d⁴).

Their normalized chart b=1 has exact Groebner basis [1]. On b=0,d=1 the basis is also [1], and b=d=0 forces c=0 from the quadratic coefficient. Thus there is no nonzero invariant constant-permanent direction. Exact generator/results: c3_invariant.py/log.

For a primitive cube root w, one nontrivial character space consists of matrices

    [0, u, u*w, u*w²;
     u, v, q, q*w²;
     u*w, q, v*w, q*w;
     u*w², q*w², q*w, v*w²].

Here the linear, quadratic and quartic coefficients vanish automatically, while the cubic is

    2q³-3q²v(w+1)+6qu²w-6quvw+3u²v+6uv²+v³.

This projective cubic is smooth: on q=1 its three derivative equations together with w²+w+1 have exact Groebner basis [1]; on q=0 the derivatives directly force u=v=0. Hence it has no linear factor over the complex numbers and its zero set contains no two-dimensional vector subspace. The conjugate character space has the same property.

Any three-dimensional plane stable under this 3-cycle splits into its three character spaces. It cannot contain a nonzero invariant vector, and distributing three dimensions among the other two character spaces forces a two-dimensional subspace in one of them, which the smooth cubic excludes. Thus no C3-stable three-plane solves the target. This does not exclude arbitrary planes lacking the symmetry. The larger seven-variable C3-stable chart computation was stopped once the invariant-line obstruction made it unnecessary.

## Independent review and additional completed checks

The C3 obstruction was independently checked by agent `/root/fresh_main_proof/c3_review`, with a second permanent implementation using Ryser's formula. Its review is `c3-review.md`, completed 2026-11-25 09:55:56 UTC. This is the only child agent spawned by this branch across both assigned gaps; the same child was subsequently reused for C2-stable planes.

The separate verification of all twenty-four zero-diagonal plane extension calculations completed with twenty-four PASS records. For every plane it computes a Groebner basis of the remaining coefficient ideal and verifies that a power of every linear form annihilating the original plane belongs to that ideal. Thus the radical condition forcing every extension direction into the original plane is checked directly. An initial run stopped at a rational-coefficient coercion error; explicitly using the rational polynomial domain fixed this, and the full rerun completed. Script/log: `fresh/planes_extend_verify.py/.log` under scratch.

A chart-independent numerical search used an orthonormal basis of the full nine-dimensional tangent space and represented a candidate plane by a complex 9-by-3 matrix. Nine real Hermitian Gram conditions fixed its columns to an orthonormal frame and prevented rank collapse. All thirty-one homogeneous permanent coefficients were included, with an analytic Jacobian checked against finite differences (relative error about 5e-10). One hundred random starts completed in about 146 seconds without a root; the best residual remained around 0.0013. These numerical failures do not prove nonexistence. Script/log: `fresh/numeric_grassmann.py/.log`.

## A nonzero-diagonal two-block plane is also nonextendable

Let r=√2 and A be the symmetric 2-by-2 matrix with diagonal (r−1,−r−1) and offdiagonal 1. Its entry sum and permanent are both zero. Therefore T(x,y)=diag(xA,yA) is a two-dimensional family satisfying permanent(J+T)=24.

For an arbitrary symmetric third direction B, subtracting a linear combination of the two seed directions allows B01=B23=0. The coefficients linear in z of permanent(J+T(x,y)+zB)−24 then express all entries of B through B11, B13, B22, B33. The exact remaining coefficient ideal over Q(√2) has a Groebner basis containing B33^5. After B33=0, its equations give B22^3=0, then B13^3=0, then B11²=0. Thus every such B is zero modulo the seed plane.

The computation also directly checks ideal membership of B11^5, B13^4, B22^5 and B33^5. This proves only that this particular two-plane has no three-dimensional extension. It does not classify all planes with nonzero diagonals. Exact script/log: `fresh/block_seed/extend.py/.log` under scratch; completed 2026-11-25 10:01 UTC. This is symbolic mathematics, not a Lean-checked theorem.

## Completed archive and general Witt reduction

The completed C2, C3 and nonzero-diagonal block-seed source/logs/reviews were copied into `results/gct231/fresh-completed/` and frozen at 2026-11-25 10:09:38 UTC. Its SHA256SUMS hash is `fb1af66897a01f010441fd273e9cf0b21ed144957611d72e538bc009bbe16699`; every listed checksum passed. A standalone independent Ryser reproducer is included. These archived files are read-only and will not be changed. The C2 result excludes transposition-stable planes; it does not by itself exclude planes stable only under a double transposition. The latter partial investigation is separately scoped in `double-transposition.md`.

A rational Witt frame for the full nine-dimensional tangent quadratic now gives an exact twelve-variable open chart. Its full ten cubic and fifteen quartic equations have been exported, and a complete family of thirty-two charts over Q(i) has a coverage argument independently assessed by finite_cases. The formula, scope, file paths and coverage argument are recorded in `witt.md`. No unit-ideal result or candidate solution is claimed for the general chart.

## Subsequent reviewed structural reductions

The earlier caveat about the twenty-four zero-diagonal planes is now resolved by the separate proof in `zero-diagonal-classification.md`: global_normal_form supplied a complete UFD/dimension argument, independently confirmed by this branch. The full classification together with the checked nonextension calculations implies that a solution three-plane must have diagonal projection rank at least two. This update does not change the earlier frozen archive.

The completed common-kernel argument in `common-kernel.md`, independently reviewed in `common-kernel-review.md` and `isotropic-kernel-review.md`, excludes every nonzero common kernel vector. Exact C4-symmetry and cubic-geometry obstructions are separately reviewed in `c4-review.md` and recorded in `cubic-geometry.md`. These remain scoped mathematical results, not a global exclusion.

Conditional on excluding independent star and triangle offdiagonal coordinate triples, the exact determinant relations reduce the remaining path case to two strata. One is excluded by the two-block obstruction; the other has fixed C4 support. Details, equation exports, and the reviewed eight-chart C4-support parameterization are in `matroid-strata.md` and `c4-support-review.md`.

The best earlier orthonormal-frame candidate was refined with tighter tolerances: its residual remained about 0.00113149, objective2.2949e-6, and gradient norm1.68e-11. An objective-Hessian diagnostic found no resolved negative curvature. This is a stationary nonzero-error fit, not a witness. A separate six-parameter C4-support numerical search completed1000 complex starts without a root, best scaled residual about0.165845. Neither numerical result supplies nonexistence evidence.

## Polar-rank and C4 factor-route continuation

The rank-one-diagonal pencil heuristic was refuted by an exact block/star pencil, and the stronger polar-rank-to-transposition-symmetry inference was refuted by a second exact pencil of polar rank six. Both particular pencils remain nonextendable. See `diag-rank-one.md`, `polar-rank-counterexample.md`, and `polar-rank-and-zero-edge.md` for exact scope and independent reviews.

The corrected C4 coordinates yield a product equation on e=0. The entire-three-plane e=0 case and all nine zero-product two-plane extension branches are now excluded by reviewed UFD, quadratic-form, and elementary polynomial arguments. The latter use the fact that two quadratic forms vanishing on a shared two-plane in a four-dimensional space have a square determinant pencil. See `c4-factor-coordinate-review.md` and `c4-zero-product-extension-review.md`.

For the nonzero-product C4 branch, the geometric normal equations are explained in `c4-nonzero-normalization.md`. The degenerate-boundary argument in `c4-nonzero-boundary.md` has independent review: alternate four-dimensional spaces cover the rank-two case, while the exceptional pure (f,H) direction and the rank-one cases give short contradictions. The remaining nondegenerate algebraic cases have small exact systems. Their finite-field computations and rational candidate substitutions alone do not prove exhaustive characteristic-zero classification; the exact QQ certificates are being handled separately by the structural and finite agents.

The separate proposed zero-edge pencil diagonal-rank bound has a robust rank-two numerical candidate and an exact rational contraction certificate establishing a nearby complex root with nonzero diagonal minor. This is an auxiliary mathematical counterexample, not a three-plane witness or a Lean-checked result; see `zero-edge-rank-two-certificate.md` for its proof scope and review status.

## Checked interfaces and compiled preservation aggregate

The binary homogeneous-linear-form factor-matching theorem is now Lean checked, including repeated factors and all six permutations. The exact C4 coordinate interface is also Lean checked: it defines the symmetric tangent matrix, proves the univariate permanent expansion and quadratic/cubic coefficient formulas, extracts their vanishing from a constant line, obtains the product identity on e=0, and reconstructs every symmetric C4-supported tangent matrix. The frozen component archives are `linear-factor-matching/` and `c4-coordinate-interface/`. These bridges do not by themselves prove the full C4 exclusion or the posted existential theorem.

A preservation aggregate built from the prior 1528-line named body and six reviewed components compiled successfully at 2026-11-25 12:09:41 UTC: exit0, 347.06 seconds, peak RSS5,589,556KiB. Its exact source hash is `455519b9fd760d5ec45d2da6274066654d1cc37123ee75c85ec6192cb54ca5a0`. The frozen 22-file archive `combined-candidate-build/` includes all component inputs, source/base snapshots, full compiler log, runner, manifest, and independent source reviews; its SHA256SUMS hash is `1e7c74f44fa747901127afd3afaa94bd0efbbd665334404aec1e8816a2974d64`. The compiler emitted only deprecation and tactic-linter warnings.

A separate V2 assembly adds the independently checked tiny triangle-axis certificate and case2/case3 scalar endpoint lemmas without introducing new imports. Its 2593-line source has hash `c99884a7311d847e0b23c4b1147c4a30bb133630a07dace51a6129675c6feee2`; all old and component inner bodies are preserved bytewise. Independent child review passed at12:09:36UTC. This branch has not compiled V2 or changed the named file: the root agent owns its named-path integration and build. The aggregate remains a scoped partial artifact, with no theorem establishing or refuting the posted existential statement.

## Exact case2 necessity bridges and current integration candidate

The six explicit case2 scalar equations now have a Lean-checked necessity bridge. It proves nonvanishing of P, B, the curve-leading factor K=P²+P−1, and the chart determinant. Exact ring certificates produce the curve-reduced affine and quadratic equations. Their quadratic/cubic eliminants share the actual remaining coordinate, so the generic common-root theorem yields two raw fixed-degree resultants equal to zero. A second checked addition proves the same in the reverse variable order. No leading-coefficient division or slope premise is used for either raw-resultant implication.

The forward source `Case2NecessaryResultants.lean` has SHA `7c6d9874977e4d112adec83a91c73bd82392d7e8ed67aefd77c385b89a8769f1`, compiled in15.31seconds; its exact-source audit passed in18.88seconds with only the three standard axioms. Archive `c4-case2-necessity/` has manifest `5640572c67451d9ddaca920f85b43f2165b3a0d49a6ba34c8f6f807d3afdbb26`. The reverse aggregate source SHA is `04284090e7df73dcdeae0b4ac44df09bce48dedce7e2f3b593ddd5b3869f7173`; it compiled in23.18seconds and audited in16.49seconds. Archive `c4-case2-reverse-necessity/` has manifest `805478602dd01970ff1d347bf088221c08a046f4769f022cf5002764c68b221b`. Both original-equation mappings and the reverse coefficient formulas were independently reviewed by finite_cases.

The child c3_review independently checked and formalized the slope boundary: F=0 and P·B·W nonzero imply that at least one of the two reduced affine slopes is nonzero. Its exact source SHA is `707e23e11549155ca65fe3d04b607d29d0d0173a277ccafef1c4a5b3c27f5480`, compilation7.93seconds and standard-axiom audit7.90seconds. Frozen archive `c4-case2-slope-boundary/` has manifest `077d9fc672e8a739b2937feb826de176291429595a4a9724638140115cd3efdd`. The five definitions shared with the necessity bridge are byte-identical.

Incremental V5 preserves the current2593-line named body and adds the independently checked projective-norm obstruction, both raw-resultant necessities, and the slope boundary. Its SHA is `1e4131977133c46f014ffb38e9b2b68e07c735d9b55ebf1ca7d3709a7de7d614`, size491914bytes,3038lines,322declarations. Independent source preservation/delta review passes. This branch leaves the named file and its final build to the root agent.

The remaining formal gap is precise: the raw resultants have not been identified in Lean with the divided projective quotients and their normalized univariate norms. The separate large projective-norm theorem therefore still has norm-vanishing hypotheses. Exact reverse quotient equalities were subsequently checked by structural_proof, but these CAS equalities are not part of the Lean bridge. No global C4 or GCT-231 conclusion is claimed.

### Correction to V3–V5 format review

Before the named build, the root agent caught that V3–V5 retained several top-level namespace blocks, contrary to CONTRIBUTING.md rule7. Their inner-body and declaration-preservation checks were correct, but this branch and its child incorrectly reported the broader format check as passing. Those candidates and diagnostic logs are preserved rather than silently changed.

V6 corrects the assembly to exactly one outer `PEqualNP.Outside.L_gct_231_aux` namespace. It preserves the current2593-line source's inner body exactly, places the norm certificate in nested `Case2ProjectiveNorm`, puts the generic common-root helper in a section, and places the necessity and slope bodies in relative nested namespaces. Every component inner proof body is preserved bytewise. Its SHA is `d2a724e6eb3c78592987233a86919f6d41e2acdcdee49b7b4c862c92b770026a`, size491683bytes,3039lines,322declarations. The strengthened static check explicitly counts one top-level namespace and requires all exterior content to be imports. Root owns the pending named build.

## Final fallback assembly

The root reported that the corrected V6 named build passed in247seconds and all322 declarations passed its standard-axiom audit. The final fallback assembly starts from that exact current3039-line source. It preserves its entire inner body bytewise and appends the checked compact star-pencil classification with residual extension, plus only the new generic modular-resultant transfer theorem. The existing common-root helper remains exactly once.

FallbackV7 has SHA `f5508fba3b3c32933c3cfa55aa9b37a944c8b76b3ad031143e5ecae9bb5e30e2`,504298bytes,3133lines,326declarations. Its checker explicitly verifies one outer auxiliary namespace,33 imports and no other exterior content, scoped opens/options, and no duplicate declarations. The only new import is `Mathlib.Algebra.Field.ZMod`. Child source review passed; root owns the final named build.

The proposed compact modular replacement of the existing201KB case2 norm certificate had not compiled by the assembly decision. The fallback therefore retains the already checked certificate. Uncompiled case2/case3 modular applications are not silently added. The generic modular transfer theorem is independently compiled, audited, and reviewed, but the final artifact remains partial and does not assert the main theorem.
