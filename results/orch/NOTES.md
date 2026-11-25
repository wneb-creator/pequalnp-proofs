# L-gct-231 orchestration notes

Lease assigned 2026-11-25 09:17:23 UTC. Only root calls the desk.

Goal: a complex linear subspace of symmetric 4 by 4 matrices, dimension 3, with permanent of J + t equal to 24 for every t in the space.

Strategies:
- root: direct algebra and integration.
- construction_algebra: rank-one/isotropic and explicit algebraic construction.
- construction_search: computational sparse/block/root-of-unity parametrizations.
- geometry_route: Hessian/higher-degree constraints and scout notes.
- lean_setup: Lean subspace dimension and construction APIs.
- rules_review: independent review and permanent API scouting.

Append timestamped findings here; use unique files in results/orch/lemmas. Coordinate before touching the final proof file. All helpers in final proof must be in its own namespace, main fully qualified theorem last. No other tracked file belongs in final PR diff. Archive working results in branch history before final single-file cleanup.

Environment is ready: pinned Lean 4.36.0 and full prebuilt Mathlib cache, checklemma and PEqualNP.Defs built. ELAN_HOME=/tmp/oec/pequalnp-pilot-79/elan; PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-79/pnp-build; PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-79/elan/bin/lake; LAKE_ARTIFACT_CACHE=false. PATH begins /workspace/pequalnp-proofs/tools/bin:/tmp/oec/pequalnp-pilot-79/elan/bin.

## Rules reviewer / lemma scout, 2026-11-25 09:20 UTC
- Current gh structured search finds no open PR for L-gct-231.
- Mathlib Matrix.permanent is a sum over permutations; no direct Fin4 expansion theorem there. Existing local proof L_gct_221.lean has compact six-product perm4 helper; L_gct_222.lean has explicit 24-term helper. Copy into own namespace if useful; these outside modules are not allowed imports for this gap.
- Enumeration helper: sum_perm_succ follows from Equiv.Perm.decomposeFin.symm.sum_comp and Fintype.sum_prod_type. Expand with Fin.sum_univ_succ, Fin.prod_univ_succ, decomposeFin_symm_apply_zero/succ, Fintype.sum_unique, then simp +decide [Equiv.swap_apply_def] and ring.
- Final helper declarations must be inside PEqualNP.Outside.L_gct_231 or its _aux namespace, with matching named end; final theorem is fully qualified and last outside namespace. Guard: node .github/scripts/outside-guard.mjs imports FILE IMPORTS_JSON PR_RELATIVE_FILE check.

## Lean construction APIs / 2026-11-25 09:19 UTC
- Checked partial `results/orch/lemmas/Dimension.lean` compiles (exit 0; scratch log dimension-test.log).
- Dimension: take range of F : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ); after proving injectivity, `rw [LinearMap.finrank_range_of_inj hF]; simp` gives finrank 3.
- Generic threeSpanMap A B C packages x₀ A + x₁ B + x₂ C as a linear map. Scalar-linearity simp must include RingHom.id_apply.
- Generic permanent_four supplies the full 24 monomial expansion, using sum_perm_succ and the checked route from L_gct_221. Direct simp with Finset.univ_perm_fin_succ loops; avoid it.

## Computational construction search / 2026-11-25T09:20:34.239381+00:00
- Exhaustive symmetric direction entries in {0,1,-1}: exactly 12 constant-permanent lines up to sign; these are star differences. Their compatibility graph has 12 edges and four triangles, all spanning only dimension2.
- The standard 2D star-sum-zero space cannot extend to a constant-permanent3-plane. Full symbolic extension constraints force any additional B back into that space.
- Gaussian-unit direction enumeration in progress; scripts and full logs in job scratch search_gaussian.py/log.

## Algebraic construction route / 2026-11-25T09:21:53.447007+00:00
- S4-equivariant standard3D family t_ii=r a_i, t_ij=a_i+a_j with sum a=0 fails: quadratic factor r²+8r+4 and cubic factor r³+6r²+12r−8 have no common root.
- Rank-two family t=v wᵀ+w vᵀ, sum v=v·v=v·w=0, kills linear/quadratic terms but not cubic/quartic generically; v=(1,i,-1,-i) tested explicitly.
- Direct sum of independent2×2 level lines (block [[√2−1,1],[1,−√2−1]]) has no3D extension: exact CAS linearization leaves quotient4vars; homogeneous Groebner ideal is zero-dimensional with terminal relation p3^5. Full scratch extend-block-quotient.py/log; not yet Lean checked.
- For centered symmetric t1=0, write t=H B Hᵀ with H the three nontrivial Hadamard columns and B symmetric3×3. Then perm(J+u t)=24+16u² tr(B²)+64u³ perm(B)+u⁴perm(t). Shared this reduction with geometry agent.

## geometry_route findings
- Natural S4 standard3plane t_ii=r*x_i, t_ij=x_i+x_j, sumx=0 fails: q requires r^2+8r+4=0, cubic requires r^3+6r^2+12r-8=0; no commonroot.
- Star2plane cannot extend: all admissible tangentS bottom3block constantq, S00=-2p-9q, p=sum starentries; quadratic2(p^2-6pq-63q^2), cubic4q(p^2-6pq-39q^2), quartic2q^2(p-9q)(p+3q), hence p=q=0.
- Full Hadamard tangent t=H B H/4 with B00=0, B=[[0,x,y,z],[x,a,d,e],[y,d,b,f],[z,e,f,c]] has q=tr(C^2)-6(x^2+y^2+z^2); full expansion scratch hadamard-tangent.txt.
- Pointwise transposition-invariant3planes: all8 exact Witt charts inconsistent, GroebnerBasis([1]) over QQ(i,sqrt2). Scripts/logs scratch transposition_planes.*. This is CAS evidence, not Lean proof.
- Testing transposition-stable3planes with anti-invariantline plus invariant2plane now; anti-invariantlevel lines have representative star signededges or diag(-4,4)+star signededges.

## Computational construction search / 2026-11-25T09:26:51.251098+00:00
- Gaussian-unit exhaustive direction search completed: 30 constant-permanent lines up to unit scaling; compatible-pair graph still has only12 edges andfourtriangles, allrank2. No3plane inthatdiscretealphabet.
- FullGrassmann numericalsearch completed1000 complex randomstarts acrossrandompivotcharts. Eachchart fixes3coordinates asidentity, hencecannotcollapsebasisrank. Nozeroresidual; bestnorm6.56e-4. This issearch evidenceonly, notrefutation. Code/log/bestmatrix: scratch search_numeric.py, search_numeric.log, numeric_best.json.
- Forstarline t01=−t02, first-orderextensionconstraints pluscoefficient x²z²=(B13−B23)² force rows1,2ofB equalexceptcol0. Quotientbythatstarline has5coords(u,d,h,i,j), qmatrixdet144 andrationalWittindex2. Thus3spacecontainingastarline reducesto2planeonquadric5 withcubic/quarticconstraints; couldtestfourWittchartsby3-variableGroebner. Not yetdone.

## Independent review / literature scout, 2026-11-25T09:26:55.829143+00:00
- StarPlane.lean independently approved as a dimension-2 partial, not the dimension-3 target. Its current _star namespace is archival only; final integration must rename into L_gct_231 or L_gct_231_aux and descendants.
- No general symmetric affine permanent-level dimension bound n-2 located in bounded searches of allowed GitHub/pequalnp hosts. Such a theorem remains UNVERIFIED; the search result is not evidence of nonexistence.
- Related checked local statements: L_gct_121 excludes symmetric rank-one J-level directions via unequal-support necessity; L_gct_109 bounds 3x3 doubly-centered spaces by 1; L_gct_216 bounds 4x4 doubly-centered spaces by 3. None alone supplies the required symmetric bound or converts symmetry to centering.

## Isotropic common-kernel route / 2026-11-25 09:27 UTC
- For common kernel u=(1,-1,i,-i), symmetric Tu=0 plus total-entry sum0 gives dimension5. The quadratic permanent coefficient has rank2 and discriminant 24(x₂+2x₃+x₄)².
- Its two maximal isotropic4D hyperplanes split over Q(i,sqrt6). Exact cubic/quartic gcd is1 on BOTH hyperplanes. Thus no constant-permanent3-plane with this fixed common kernel. This is CAS evidence with algebraic reasoning, not Lean checked.
- Reproduction: scratch common-kernel-isotropic-gcd.py and complete log. Trying special kernel (1,omega,omega²,0) next.

## Algebraic follow-up / 2026-11-25T09:27:49.923448+00:00
- No Klein-four-stable3D candidate: selecting one isotropic line from each nontrivial character leaves8 choices; all nonzero cubic. The invariant tangent component has no nonzero full level line.
- All arrowhead-supported3D spaces are obstructed, by separating rank of projection to three leaf diagonal entries. Rank3 forces b=βe etc and incompatiblequadratic identities; rank1 contains star2; rank2 reduces to g=0 (Sym3 support) or e+f=0, where a nonzero mixed quadratic coefficient survives. These are mathematical derivations, not Lean-checked.
- Copied exact block-extension Groebner script and full log to results/orch/lemmas/algebra-extend-block-quotient.py/.log. Last symbolic solve was stopped after zero-dimensional Groebner result, as redundant.

## Three-plane search / 2026-11-25T09:28:09.306432+00:00
- V4-equivariant candidate: each nontrivial weight direction Sym(h0,hr)+k Sym(hj,hk) has quadratic coefficient32(k²−3) and quartic64(k²+1)², so no such nonzero constant line.
- C4-equivariant candidate3planes (one line in weights1,2,3) have coefficient ideal Groebner basis1; weight0 has no good line. This excludes symmetry-restricted planes only.
- Centered t=H B Hᵀ: independently verified cubic coefficient64per(B). Parameterizing maximal-isotropic B-spaces by d=(I+K)x, o=(i/√2)(I−K)x for skew3×3 K, the10 cubic coefficients have Groebner basis1 in each parity of off-coordinate signs. These8 natural Witt charts seem to cover both OGr(3,6) components, but coverage is not yet formalized. Scripts centered_ogr_search*.py/log in scratch.
- Full-Grassmann numeric search was stopped as duplicate of construction_search; 117 starts found no zero, best residual6.56e−4. This is evidence only.
- Dense Gaussian line extension has quotient dimension6 with3 rank6 quadratic constraints, determinant pencil splits2+4. Exact formulas in dense_line_extension.log.

## Common-kernel route: finite reduction and obstruction / 2026-11-25 09:32 UTC
- Both hyperplanes for u=(1,omega,omega²,0) also have cubic/quartic gcd1 (common-kernel-omega.py/log).
- For centered isotropic u, write p=e3(u), q=e4(u), e=ones/2, B=euᵀ+ueᵀ, E=uuᵀ. Any desired3-plane must contain B+beta E because it cannot contain E. Its cubic coefficient is6p(beta³p+1); quartic is3/2(16beta⁴q²+16beta³pq+3beta²p²+2q). Resultant:4374p⁴(p⁴−8q³)(27p⁴−512q³).
- If p!=0 normalize p=-1,beta=1. Then q=3/8 or1/2. Let z0_i=u_i³−(4q/3)u_i²+3/4 and D=z0uᵀ+uz0ᵀ. Every candidate3-plane contains bB+dD+(b+Gd)E. For q=1/2, vanishing b³d and b²d coefficients requires G=7/6 and G=8/9. For q=3/8, they require G=1/2 but bd² coefficient is9(2G²−2G+1), nonzero. Thus no centered-isotropic common-kernel3-plane. p=0 is scaled/permuted earlier four-root case. This is exact CAS plus algebraic reasoning, NOT Lean checked.
- Full computation common-kernel-ratios.py/log uses resultant P(X,Y,Z)=product_i(X/2+Y u_i+Z z0_i) and permanent Cauchy-Binet sum of alpha! times coefficients of P and P(KX). Each4D isotropic hyperplane has Groebner basis[1], but simple contradictions above suffice.
- Does NOT exclude all common kernels: when u·u!=0, exceptional projection norms k=4−(sumu)²/(u·u) include k=1 (quadratic rank3/radical2) and k=0 (isotropic projection, possible rank4/radical1).
