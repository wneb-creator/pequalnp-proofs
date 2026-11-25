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

## Exhaustive finite-field diagnostic / 2026-11-25T09:32:39.265307+00:00
- Over F5: checked488281projective tangentdirections;3918constantdirections;2340compatiblepairs;156distinct2Dlevelspaces;ZERO3Dlevelspaces.
- Over F7: checked6725601projective tangentdirections;17088constantdirections;6608compatiblepairs;236distinct2Dlevelspaces;ZERO3Dlevelspaces. F7containsprimitivecube roots, so covers thatsmall-fieldsymmetrycase.
- Paircompatibility usesgradientpolarizations for homogeneousdegrees2,3,4 plus quartic(A+B); then a3plane existsiffa third direction iscompatiblewithall projectivedirections of a2plane. Degrees<fieldsize ensure finiteevaluation identifies polynomialrestrictions. Scripts/logs/data archived inresults/orch/lemmas/finite5-* andfinite7-*.
- Every2Dlevelspace inbothcensuses hasinjectiverow-sum map(rank2). Mostlackcommonkernel: F5commonkernel0:148,1:8;F7commonkernel0:196,1:40.
- These finite-fieldcomputations are not acomplexrefutation andnotLeanchecked. Complexpoints couldreduce onlyoverextensionfields.

## Computational search / 2026-11-25T09:32:56.182679+00:00
- All four rational Witt charts for the star-line extension quotient produced Groebner basis [1] over ZZ. This is a CAS result only; it has not been formalized in Lean. Script and full log: scratch star_line_groebner.py and star_line_groebner.log.
- A 2-plane isotropic for H plus H plus <1> must have an invertible projection choosing one coordinate from each hyperbolic pair. If every such cross-pair minor vanished, either the hyperbolic projection would have rank at most1 (forcing a forbidden pure anisotropic vector) or it would lie in one hyperbolic pair, whose rank2 form cannot cancel one square. This explains the four-chart cover used by the CAS test.
- The full 12-variable isotropic chart is being searched numerically with analytic Jacobians (verified by finite differences). A second run changes the chart by random orthogonal transformations, preserving the quadratic constraint. No exact 3-plane has been found.

## Three-plane search follow-up / 2026-11-25T09:33:13.127189+00:00
- Computed a degree2 Nullstellensatz certificate: ten centered OGr chart cubic-coefficient polynomials sum to1 with explicit polynomial multipliers modulo h²+2. Verified exactly in Sympy; not Lean checked. A symmetry-reduced certificate and generator scripts/logs are archived under results/orch/lemmas/three_plane_centered*.
- C3 action: the nontrivial weight3-space has cubic3(4a³+12a²b+3c(a+b)²+2c³), a smooth plane cubic, so it contains no2D linearzero space. The trivial-weight tangent3-space has no good line; all three affine projective charts have coefficient GB=[1]. This excludes C3-invariant3planes, not arbitrary planes.
- No explicit3-plane construction found. All computational exclusions are restricted-family evidence; none establishes the assigned statement false.

### geometry_route global charts
- Constructed exact isotropic OGr(3,9) bigcell with12parameters: p∈C³, w=M p=(c,f,z), D=diag(1,2,-6), r=A p-(1/4)MᵀD M p, A skew. a=p0+r0,b=i(p0-r0),d=p1+r1/2,e=i(p1-r1/2),x=p2-r2/6,y=i(p2+r2/6). q=4p·r+wᵀDw=0.
- Retaining full3×3dualR gives18variables,31polynomialconstraints degree≤4 and5,409monomials; eliminating6qrelations gives12variables butdegree≤8 and70,772monomials. Inputs full-ogr18-mod97.{json,msolve}, exactQQ(i) encoding full-ogr18-rational.msolve (19variablesincludingii,ii²+1).
- Global32chartcover possible overQQ(i): leftover(c,f,z)=p3*(2,1,1)+(r3/6)*(2,1,-1)+h*(1,-1,0), so q=4Σ_{0≤i<4}pi*ri+3h². Choose3distincthyperbolicpairs andonecoordinateeach:32chartflags. Cover follows independenttransversal/Rado plus isotropicdimensionbounds in3D and5D. Not yet formalized.
- FastF4 modulo97 (i=22) running via compiledneogb; degree6round1s, degree7currentlylarge. Bounded4GiB180s. No globalverdict yet; finitefield inconsistency alone would not establishcharacteristic0refutation.

## Exact row-sum graph chart / 2026-11-25 09:34 UTC
- Parameterized symmetric C entries as independent linear forms in row coordinates(x,y,z),18parameters. Substitution into Hadamard permanent yields31constraints:6quadratic,10cubic,15quartic;2,071expandedterms after primitive normalization.
- Inputs scratch rowsum-graph-mod97.msolve and rowsum-graph-rational.msolve; alternative DRLvariableorder groupsbydirectionin rowsum-graph-columnorder-{mod97,rational}.msolve. Exact sparseJSON and generator saved. Formula independently verified at5rational matrices.
- rules_review coordinatingF4run. This is onlythechart where row-sum projectionhasrank3; globalcoveragewouldrequire provingrow-sum injectivity forlevel3spaces.

## Computational searches completed / 2026-11-25T09:34:52.758967+00:00
- 1,000 complex full-Grassmann starts: no solution, best residual6.56e-4.
- 5,000 complex starts in the 12-variable exact-quadratic Witt chart: no solution, best residual9.78e-3.
- 2,000 complex starts across100 generic orthogonal changes of the Witt chart: no solution, best residual3.18e-4. Changes used a compact real orthogonal group after complex diagonalization of the quadratic form, keeping conditioning bounded.
- These numerical results are heuristic evidence only. Each chart fixes an injective projection, so an apparent solution could not merely collapse the three basis directions to dimension2. All complete stdout/stderr logs and source scripts are saved in job scratch.

## Lean-checked centered chart obstruction / 2026-11-25T09:39:12.902644+00:00
- `results/orch/lemmas/CenteredObstruction.lean` compiled successfully with exit0. It is34 lines and proves that h²+2=0 plus the ten exact centered-chart cubic coefficient equations implyFalse.
- The certificate is an integer polynomial identity with right-hand side31578, verified by Lean linear_combination, followed by norm_num. This proves one algebraic chart obstruction only; it does not prove chart coverage or refute L-gct-231.
- Full compile output is empty and preserved at scratch centered-obstruction-build.log; compilation command was lake env lean ../results/orch/lemmas/CenteredObstruction.lean with the documented environment.

### geometry_route bounded GB status
- GlobalWitt18mod97F4 stopped atdegree8 afterdegree7matrix238597x446773; noresult.
- Genericrowpair2plane graph (normalu=(0,1,2,-3), rowbasis(1,-2,1,0),(-4,3,0,1)):12variables12eq1015terms, mod97F4 capped180s atdegree10matrix219366x342463; noresult. Exactrationalinput generic-rowpair-rational.msolve available.
- Firstorderthird-row extension:18variables21eq2435terms, eliminate6C3variables,maxpairs256,4GiB180s. Reacheddegree7large matrices; noverdictwithinbound. Input generic-rowpair-extend-{mod97,rational}.msolve.
- ImportantAGcaution: finitefieldobservations do NOT implyallcomplex2planeshaveinjectiverowsum. Fano2dimension argument suggestscomplexboundary2planes exist. Couldinsteadboundboundary2planes tofinite andexclude3planesofrowrank≤2.
- No globalproof/refutation obtained. AllCASclaims are exactcomputationalexperiments butnotLean-checked.

## Finite-field boundary and extension checks / 2026-11-25T09:45:08.021857+00:00
- A conjectured restriction on row-sum images from F5/F7 was disproved over F11: for the fixed generic normal (0,1,2,-3), exhaustive search found three level 2-planes, each with row-sum rank 2. Their common linearized extension spaces have dimension exactly 2, so none extends to a 3-plane, even after extending the field.
- Boundary search enumerates every centered constant direction B, then every projective compatible A modulo B. The linear constraints are the gradients of the degree 2, 3 and 4 coefficients at B. Testing A and A±B kills every remaining mixed coefficient for characteristic greater than 3. Counts: F11 has 84 centered lines; F13 has 200; F17 has 252; F19 has 272. None extends to a level 2-plane over its base field. This does NOT prove the complex boundary empty; a projective dimension argument indicates complex boundary planes must exist.
- Random F13 search sampled 3026 constant directions and found 15 distinct level 2-planes, none extending to a 3-plane over F13. Five had larger linearized extension spaces.
- The nontrivial nullity-4 example lifts over Q: A01=1, A12=A13=-1/2, B02=1, B03=-1. Its exact extension quotient has coordinates p0,p1 and Groebner basis [4p0²-12p0p1-63p1², p1³], so it has no extension over C either. The other nullity-4 examples are permutations of this crossed-star plane or the ordinary star plane.
- Scripts, complete logs, and small plane lists are archived under results/orch/lemmas. None of these computational diagnostics is a Lean refutation of the full statement.

## Lean-checked star-plane maximality / 2026-11-25 09:49 UTC
- `results/orch/lemmas/StarMaximal.lean` compiles with exit0, empty log. Main lemma in namespace L_gct_231_aux.StarMaximal proves: if symmetricT satisfies per(J+star(x,y)+zT)=24 for every x,y,z, then T=star(T01,T02). Thus the checked2Dstarspace admits no linear extension. This remains a partial; arbitrary3spaces could avoid thisstarspace.
- Proof: four scalar evaluations extract first derivative; six parameter evaluations and exact linear_combination certificates force lower3×3block constantq andT00=−2p−9q. Quadratic/cubic coefficients forceq³=0, thenp²=0, finishing allentries. No additional axioms or unchecked computation.
- File frozen for root review andearlypush. Full buildlog star-maximal-build.log; CAS derivation star-maximal-generate.py/log/data.json is supplementaryonly.

## Checked crossed-star certificate / 2026-11-25T09:53:34.218912+00:00
- CrossedStarObstruction.lean compiles with exit 0. From q=4u²−12uv−63v²=0 and c=v(4u²−12uv−39v²)=0, the certificate c−v*q=24v³ forces v=0 and then u=0. This checks the polynomial obstruction, not the full classification of all level 3-spaces.
- The dense Gaussian centered line is equivalent to three_plane_search’s existing case; duplicate SymPy Groebner work was stopped and that agent owns its exact closure computation.
- A numerical complex boundary 2-plane found by three_plane_search was independently checked: its centered direction has zero row sums and sampled permanent residuals are about 1e-13. Its extension matrix has numerical rank 7, with smallest nonzero singular value about0.0966; no third direction is apparent.

## Dense-line exclusion and complex boundary candidates / 2026-11-25T09:55:11.245128+00:00
- Dense Gaussian centered lineA fromearliersearch has NO independent2plane extension accordingto exactrational F4. Projectivizingits6Dquotient viafirstnonzero coordinate yields6strata; allreturnbasis[1]. Largeststratum took23.89seconds, others≤0.063seconds, under1GiB/120CPU-second caps. ThisisCAS evidence, notLeanproof. Inputs/logs/results archivedasthree_plane_dense-boundary-* andgeneratorfiles.
- Nevertheless a general centeredB plus independent tangentA yields a square12-variable boundary2plane system. Firstnumericalstart foundresidual3.03e-14; highprecisionNewtonrefinement reached1.51e-86 at90digits. B00=1,A00=0,A01=1 enforceindependence. Files three_plane_boundary_numeric_best.json andthree_plane_boundary_refined.json containmatrices. NOTanexactalgebraicorLeanresult.
- The candidate common linearized extension has numerical nullity 2 (third-smallest singular value 0.0195); the boundary Jacobian is numerically full rank (smallest singular value 0.000454). These diagnostics suggest isolation and detect no third extension direction; they do not prove either assertion exactly. Further bounded sampling checks other roots for nullity at least 3.

## Boundary search completed / 2026-11-25T09:56:13.528659+00:00
- The bounded numerical search finished after 110.14 seconds: 458 starts yielded 358 distinct normalized boundary 2-plane candidates. Every candidate had common linearized extension nullity 2; the smallest third singular value was 0.01513. No potential extension to dimension 3 was found. These are numerical candidates, not exact or Lean-checked solutions.
- Source, complete output, and all numerical roots are archived as `results/orch/lemmas/three_plane_boundary_sample.py`, `.log`, and `three_plane_boundary-sampled-roots.json`. The first candidate was refined to a residual of 1.51e-86 at 90 digits, but its exact algebraic coefficients remain unknown.
- An exploratory Schubert calculation gives degree 104832 for the row-rank boundary intersection: the coefficient of x^8 y^7 in (x-y)(x²+xy+y²) times the top Chern products for Sym², Sym³, and Sym⁴ of a rank-2 bundle. The intersection-theoretic assumptions and this interpretation have not been formalized.

### Long F4 result
Sole rowsum18mod97 LA44 probabilisticsparseF4,2threads,maxpairs512,8GiBAS: SIGXCPU exit-24 after1066.7swall (17.8min). RequestedCPUcap1200s;lastobservedCPU1232.04s beforekerneltermination. Stilldegree8,120140pairbacklog;lastcompletedmatrix150779x346669. Observedpeakvirtual2.47GiB/RSS2.09GiB. NoresultJSONorGBverdict. Fulllogandstatus: rowsum18-long-la44.log/status.json. Allmycomputeprocessesstopped.

## Algebra finite-field Fano-surface diagnostics (2026-11-25T10:07:44.324404+00:00)

All computations are diagnostics over finite fields, NOT complex proofs. Full scripts, stdout/stderr logs, and exact plane bases are archived as `lemmas/algebra-fano2-*`, `algebra-star-incidence-*`, `algebra-classify-rank2-*`, and `algebra-rank2-*`. The coefficient Jacobian has 18 basis-entry columns and12 polynomial rows; its GL2 gauge kernel was checked for every plane.

Complete F5 census:156 planes, Jacobian rank counts7:4,9:16,10:72,11:32,12:32 (14 S4 orbits). Complete F7 census:236 planes, ranks5:24,7:28,8:24,9:60,11:60,12:40 (15 S4 orbits). Three generic fixed-row-image F11 planes have ranks11,12,12 and all extension kernel dimension2. Exact rational ordinary star plane has Jacobian rank7; crossed-star plane rank9. Thus Fano-surface singularities are abundant even in characteristic zero.

Let K be the common kernel of all polarized gradients along a plane. Combined condition rank(J)<12 and dim(K)>=3 holds for104 F5 and136 F7 planes. EVERY ONE contains a rank<=2 matrix over the algebraic closure. More strongly EVERY ONE contains a rank<=2 matrix at which all TEN full symmetric permanent quartic partial derivatives vanish. This was tested by exact gcds of16 binary cubic minors plus10 binary cubic permanent-gradient entries, including the projective point at infinity. There were zero exceptions; the8 smooth planes with Kdim3 in each field have no such direction.

There is already a characteristic-zero curve of singular/K>=3 planes through the simple star A01=1,A02=-1. Compatible B can take form [[a,u,0,d],[u,h,h,i],[0,h,h,i],[d,i,i,j]], a=-2u-2d-4h-4i-j. Permanent(J+sA+tB) is independent of s, leaving3 homogeneous equations in5 coordinates, hence at least a projective curve. Therefore isolated-singularity or universally Kdim2 arguments cannot work.

Rank-two singular permanent classification (mathematical derivation shared with fresh_geometry, not formalized): for T=uv^T+vu^T, gradient cofactors pair binary cubics F_i=product_{j!=i}(u_j X+v_j Y) by a nondegenerate symmetric antidiagonal pairing. If every row is nonzero, isotropic span(F_i) has dimension<=2, so at most two projective row types. A2+2 partition is impossible: for finite ratios a,b the diagonal cofactor equations give8a(a^2+4ab+b^2)=8b(a^2+4ab+b^2)=0 and a cross cofactor2(a+b)(a^2+10ab+b^2)=0; with an infinite ratio a mixed cofactor is2 after scaling. A3+1 partition forces a star with possible center diagonal. The level linear constraint d+2s=0 and quadratic coefficient d^2/2 force d=0. Thus full-support rank2 singular level directions are ordinary centered stars. Remaining directions have a zero row/column and reduce to3x3 symmetric matrices with sum=0, quadratic level coefficient=0, permanent=determinant=0, typically a curve.

## Centered 2-plane subproblem / 2026-11-25T10:08:57.643691+00:00
- Natural Witt coordinates: diagonal d=u+v, complementary off-diagonal o=(h/2)(u-v), with h²+2=0. The centered quadratic is4u·v. Set u0=x,u1=y; retain arbitrary linear forms for u2 and all three v coordinates. This gives8 parameters and12 coefficient equations (3 quadratic,4 cubic,5 quartic).
- There are12 coordinate charts, choosing one endpoint from each of two distinct hyperbolic pairs. Pair permutations and even off-diagonal sign flips come from original S4 vertex permutations and preserve both permanent constraints. The unused third pair compensates an odd selected endpoint flip. Agent three_plane_search independently confirmed this coverage/symmetry argument.
- F4 overF97 with h=17 returned the unit basis[1] in0.16s. Explicitly eliminating the3 quadratic relations gives5 parameters and again unit basis in0.18s. These are CAS computations, not Lean-checked proofs.
- Rational F4 with h²+2 retained timed out at120s for both8-parameter and5-parameter variants. A distinct rational --la1 retry faulted with signal11 under1GiB after79s; no rational basis or mathematical verdict was produced.
- Complex Lean grind trials (ordinary and only, with different ring-step budgets) reached120s without a verdict at -M2048 and3GiB RSS cap. Trivial diagnostics failed at -M768 and passed at -M2048, so the lower limit was below required startup capacity. Earlier approximately822MiB RSS figures were incomplete Lake-parent measurements, not complete Lean process-tree peaks; the monitor has been corrected to include children of all worker threads. A ZMod97 grind trial is now pending.

## Fresh geometry, 2026-11-25 10:07 UTC

- Every dense star direction is excluded from any candidate three-space by a rank-three quadratic on the four-dimensional image of the lower block. A two-dimensional isotropic image must contain its radical J₃, which contradicts the affine level condition. The exact derivation is in lemmas/fresh_star_direction.md; scratch fresh_star_verify.py/log checks the key identity.
- The two outstanding noncentered common-kernel possibilities reduce to an unavoidable rank-one radical or a two-dimensional radical zwᵀ+wzᵀ with Σz=z·z=1 and Σw=z·w=0. An elementary alternating cubic identity on every three coordinates forces z to have a repeated entry. The quartic leaves only the coordinate-unit case, which contains the checked star plane. Full argument in lemmas/fresh_nondoubly_centered_kernel.md. No completed Lean proof of these new exclusions.
- S4-invariant affine row-chart Macaulay searches over F97 found no unit certificate at total degrees seven and eight (20,242 and 65,662 invariant columns). Total degree nine reached the 120-second cap before elimination finished. This is bounded-degree finite-field evidence. A local 220×500 Plücker cubic matrix ruled out tangent nets with a common line for all eight smooth split rank-two direction orbits enumerated over F13, as checked in scratch fresh_rank2_net13_plucker.log.

## Algebra invariant test and rational rank-two obstruction (2026-11-25T10:10:48.175063+00:00)

The proposed invariant identity does NOT exist: after total entry sum zero, the17 quartic polynomials per(T), tr(T)*cubicCoeff(T), and15 products of Q=[tr(T)^2, sum diagonal^2, sum rowsum^2, sum diagonal*rowsum, Frobenius-square] have exact rational coefficient-matrix rank17, while adjoining det(T) raises rank to18. Matrix size495x17. Archived algebra-quartic-invariant-identity.py/.log.

A simple nonstar rank-two singular-level direction is the top-left3x3 block [[0,1,-1],[1,-4,0],[-1,0,4]], fourth row/column zero. Exact rational algebra shows this direction cannot belong to any desired3space: its space of linearly compatible B modulo A has dimension6; imposing all six remaining homogeneous coefficients gives a54-element exact grevlex Groebner basis with affine Krull dimension1. Hence finitely many projective2plane extensions; a3space would yield P1. Equivalently, adding the linear equation B23=0 (coordinate w5=0 in the saved quotient basis) gives a zero-dimensional homogeneous ideal in5 variables, whose only point is zero; its32-element GB includes w3^8 and w4^6. All source/full stdout logs archived as algebra-extend-rank2-three.*, algebra-rank2-three-gb-dimension.*, algebra-rank2-three-hyperplane.*, and the exact six equations/basis in algebra-rank2-three-extension.json. This is a CAS mathematical obstruction, NOT a Lean-checked theorem.

Further explicit nonstar singular rank-two level directions arise as3x3 blocks [[0,1,r],[1,2/(r-1),0],[r,0,-2r^2/(r-1)]] for r=±i or2±sqrt(3). The remaining quadratic level coefficient factors as2(r^2+1)(r^2-4r+1)/(r-1)^2.

## Conditional rank-two singular incidence and row-chart search / 2026-11-25 10:15 UTC

- Every possible symmetric rank-two singular-permanent level direction has now been classified for local extension testing. The condition that every candidate three-plane must contain one of these directions is still unproved. Details of the local arguments in lemmas/fresh_singular_rank_two.md.
- Zero-row directions with invertible 3×3 permanental cofactor matrix force a two-dimensional level space supported on a principal 3×3 block. Exact rational unit ideals in all four Witt charts rule those out (scratch fresh_sym3.py/log). The repeated-row exceptional type has one Galois/permutation orbit, excluded by a full-rank cubic Plücker system at the simple reduction k=4,r=17 mod23 (scratch fresh_repeated23.log). The separate two-vertex type was handled by construction_algebra.
- S4-invariant row-chart degree nine completed mod97, rank152578 on196049 columns; the constant is outside the row space. Complete elimination took239s. This bounded-degree test does not settle the row chart. The linear projective stabilizer Lie algebra already for q,c is zero modulo scalars (scratch fresh_stabilizer.py/log).

## Single support-two direction obstruction via complete projective fiber (2026-11-25T10:18:26.544881+00:00)

Let R=Z[1/2,rr]/(rr^2-2), an integral domain, and let A have top-left2x2 block [[rr-1,1],[1,-rr-1]], all other entries zero. Since (rr-1)(rr+1)=1, fixing B00=0 defines a valid A-gauge over all R. The total-entry-sum constraint eliminates B33, and q(A,B)=0 eliminates B01 with coefficient4, invertible in R. This gives a free rank7 quotient W of linearly compatible directions modulo A. The remaining equations are homogeneous in W with degrees2,3,2,4,3.

The candidate quotient2spaces form a CLOSED subscheme F of Gr(2,W), cut by coefficients of these five forms restricted to the tautological2space. Thus F is projective over Spec R. All21 row-reduced echelon strata (pivot pairs i<j among7 columns) were checked over F97 with rr=14, and EVERY stratum has unit ideal; the final zero-variable stratum has a directly nonzero equation. The RREF strata cover all2spaces over every field, including algebraic closures. Therefore the entire geometric fiber at (97,rr-14) is empty.

Properness now proves the characteristic-zero geometric generic fiber is empty: if it were nonempty, the closed image of F→Spec R would contain the generic point and therefore all of the integral base, contradicting the empty special fiber. No smoothness or flatness hypothesis is needed. Hence no desired3space overC can contain this single support2 A. This is a mathematically valid CAS-assisted obstruction, NOT Lean-checked. It is categorically stronger than merely finding no Fp-rational points.

All21 modular inputs, full F4 logs and outputs, generating scripts, exact quotient basis/equations, and rational checks are archived as algebra-block-single-* and algebra-rank2-block-single-extension.json. The largest10-variable modular chart took0.17s. Twenty boundary strata also return unit ideals directly overQ with rr^2=2; the generic11-variable rational chart encountered coefficient swell under the60s/1GiB bound.

### Checkpointed global row-sum F4 launch 2026-11-25T10:20:40.672566+00:00

Independent supervisor review and small tests passed. The checkpoint engine exports all non-null internal basis polynomials at stable round boundaries, always unions original generators on resume, and skips final GB minimization on partial return. Latest snapshot is atomic; previous retained only if compressed size <=16 MiB. Full diagnostics and snapshots: `/tmp/oec/pequalnp-pilot-79/rowsum18-checkpoint-la44-b2048*`. Running mod 97 / probabilistic LA44 is diagnostic and cannot establish the complex statement.

### construction_search 2026-11-25T10:22:35.903093+00:00 — centered two-plane status (research only)

The natural Witt chart has unit ideal over F97 (h=17) in both eight-variable uneliminated and five-variable q-eliminated forms; this is NOT a characteristic-zero result. Rational F4 runs with h as a variable timed out at120s in both forms; the alternative exact LA1 route faulted under its1GiB cap. Four rational physical-coordinate charts were generated, representing all15 charts under permutation of B indices: pivot pairs(a,b),(f,e),(a,f),(a,e), with coordinates B=[[a,d,e],[d,b,f],[e,f,c]]. Chart0 contains184terms but rational F4 still timed out120s. Other rational charts not yet run.

Lean diagnostic breakthrough: 13polynomial hypotheses elaborated>120s with overloaded arithmetic, even conclusionTrue. Replacing every operation by typed helper functions ca/cm/cp and balancing sums/products elaborated successfully in4.23s at1.84GiB measured fullprocess RSS. This is ONLY an elaboration probe, no mathematical theorem. Exact chart obstruction then reaches proof-producing grind. At10000steps it hit the ringSteps limit; with1000000 it hit default recursion depth in3.4s. A raised recursion-depth run is pending. Allcomplete logs retained under /tmp/oec/pequalnp-pilot-79/centered-two-*. Prior Lakeparentonly RSS observations were incomplete and must not be treated as process-tree peaks.

Checkpointed row-sum run 10:20:40–10:26:02 UTC ended gracefully PARTIAL on initial checkpoint failure. It completed two degree8 rounds, latest280904×657757,1555 new/493zero; observed peak RSS2533768KiB/VM2714540KiB. No checkpoint remains, so no reusable basis. Full status/log/result preserved; rules_review investigating explicit serialization failure diagnostics. Do not interpret this as a GB or target verdict.

## Stronger row-normal diagnostic and failed wedge identities (2026-11-25T10:27:36.719152+00:00)

Every stored plane with common gradient-kernel dimensionK>=3 has repeated coordinates in its centered row-image normal, overF5(112 planes),F7(144 planes), and the randomF13 sample(5 of15 planes). No exceptions. This includes the8 smooth Fano/K3 planes in each complete census. If this implication holds overC, a hypothetical3space with invertible row map is impossible because its2planes all haveK>=3 while their row normals sweepP2, which is not contained in the six hyperplanes n_i=n_j. This is a CONJECTURAL universal criterion, not a proof; the old claim for ALL2planes was false overC, and this stronger hypothesis is essential.

Ambient singular locusX=(q,c,p4) is larger than rank2 permanent singularity: finite directions of rank3 and4 occur. Eight F5 Fano-singular planes withK2 avoid the entire Sing(X) over algebraic closure (exact gcd of84 degree6 gradient-minor polynomials), so singular-Fano alone does not imply ambient singular incidence. All joint exceptional planes still meet rank2 permanent-singular directions.

Candidate invariant identity tested and rejected: stack ordinary-monomial gradient coefficients q0,q1;c0,c1,c2;p0,p1,p2,p3. Let uij be the Hodge scalar of q0 wedge q1 wedge c0 wedge c1 wedge c2 wedge pi wedge pj, dividing byA wedge B. F0=u03-u12/3 is degree12 and has the same GL2weight andS4sign as D(n)=product_{i<j}(n_i-n_j), but F0 is not proportional toD. Binary quartic F4=(u01,2u02,3u03+u12,2u13,u23) satisfies I(F4)=9F0^2 automatically by Plucker. A proposed D^3=aF0^3+bJ(F4) also fails finite tests: these three columns have rank3 overF7, and D=0 examples have two differentJ/F0^3 ratios overF5 andF13. Full exact values and reproducible scripts archived algebra-fano2-wedge-*.

### Further geometry observations 2026-11-25T10:28:23.144674+00:00

The global Fano scheme of3planes satisfying q,cubic,quartic is closed inGr(3,9) and therefore projective overZ. A complete empty geometric fiber modulo a prime would rule out a complex plane by proper specialization; a single affine rowgraph/fixed-rowimage chart does not have this implication, because solutions can specialize to its boundary. This is a mathematical observation, not formalized inLean and not a completed exclusion.

A small exact symbolic test found that the quartic is not in the span of the five natural S4-invariant quadratic contractions of the cubic gradient modulo arbitrary linear*cubic and quadratic*q corrections. Full log: scratch gradient-quartic-identities.log, ranks59 versus60.

Accepted L_gct_226 uses cone C=L+span(J), row projections, and dimension induction. For a symmetric4×4 target, a nontrivial kernel of an individual row projection in C yields a direction with zero row and matching zero column; quartic is then automatically zero, leaving a3×3 symmetric block with linear/q/cubic constraints. This may be a smaller global split than row-sum rank, but no classification or extension obstruction is established.

Checkpoint engine now selects complete shortest derived polynomials under a conservative512MiB output bound; original input always unioned on restart. This preserves the original ideal even when only a subset of progress is retained, and metadata states PARTIAL/subset=true with retained/total counts. Independent source review passed, six modular/elimination resume tests plus actual signals passed, forcedtinycap2-of4 polynomial subset resumed exactly to baselineGB. New long run prefix `/tmp/oec/pequalnp-pilot-79/rowsum18-subset-la44-b2048`; prior failed run remains separately preserved.

## Universal diagonal-congruence syzygy (algebra derivation, not formalized)

For P(M)=per(M), every diagonal D satisfies DP(M)[DM+MD]=2 tr(D) P(M), by row/column scaling semi-invariance. Let L be a constant-level2plane, n a centered normal to its row image, D=diag(n), E=DJ+JD. Then trD=0 and n dot rows(T)=0 forT inL, so E and DT+TD lie in the total-entry-sum-zero tangent space. Expanding at M=J+T gives, with q,c,p4 the degree2,3,4 homogeneous pieces:

- grad q(T) dot E=0;
- grad c(T) dot E + grad q(T) dot (DT+TD)=0;
- grad p4(T) dot E + grad c(T) dot (DT+TD)=0;
- grad p4(T) dot (DT+TD)=0.

This is a permanent-specific relation between the common-gradient matrix and the Fano deformation Jacobian, involving the diagonal congruence operator whose entrywise eigenvalues are n_i+n_j. It may explain the repeated-row-normal discriminant, but no implication has been proved yet.

### construction_search 2026-11-25T10:36:41.518184+00:00 — exact mixed-chart progress

The physical mixed chart(a,f)=(x,y), eight rational parameters, twelve equations and172terms, completed exact rational F4 in113.725s with basis[1]. This excludes that chart as a CAS result, not a Lean proof. The remaining mixed chart(a,e) timed out at120s. No global centered-two-plane exclusion has yet been proved. Balancedtyped Lean grind for the172term chart reached the4GiB process-tree RSS cap after9.27s; those blind retries have stopped.

A new C++ sparse Macaulay solver records each normalized pivot as inverse_leading_coefficient*(originalrow−sum dependency_coefficient*previouspivot). Reverse propagation recovers a unit-ideal witness. Three_plane_search independently checked the solver/generator/verifier. For chart2, degree6/7/8 spaces do not contain1 modulo1000000007; degree9 (37752rows,24310columns) yields a3854term witness in2.89s. Chart3 degree9 gives a3578term witness in2.7s. Both complete polynomial identities were independently checked in Python modulo that prime. These modular witnesses are not characteristic-zero certificates.

CRT with matching ordered pivot-origin/leading-column fingerprints is running for both charts, saving full resumable state after each prime. At43primes1286bits for chart2,27nonzero reconstructed rational fractions remained stable acrosssuccessiveprimes at approximately526bit height; most coefficients still had only random bounded-fraction reconstructions. Any claimed exact certificate will require an independent full integer polynomial identity after clearing denominators. Parent authorized up to20min/about200primes for this attempt.

### 10:38 UTC — three_plane_search: four row-kernel frame

- Archived mathematical reductions in `lemmas/three_plane_global_incidence.md`: the degree-13 Fano critical-plane condition, a generic complete-intersection countermodel showing why permanent-specific incidence is essential, and the general-position four-kernel chart.
- Four-kernel chart has eleven parameters after total-entry sum zero. Off-diagonal injectivity reduces coverage to triangle and path edge saturations. Cubic vanishing forces the quartic to have double zeros at the four frame points, leaving only three quartic coefficients to impose.
- Both reduced saturated charts (20 equations, 11 variables, 803 terms) give unit ideals modulo 97 in approximately 1.5 seconds each. This is finite-field evidence only. Both unreduced rational attempts hit the 120-second cap. Reduced rational attempts are still running under the same one-GiB / 120-second-per-chart limits.
- Independently reviewed the centered-two-plane Macaulay solver, matrix generator, modular verifier, and CRT driver. No arithmetic flaw found. Final exact integer polynomial identity and Lean checking are still required.

## Collinear three-zero-row-points arrowhead classification (2026-11-25T10:39:56.316459+00:00)

For S(x,y)=[[g*y,0,0,d*y],[0,i*x,0,e*x],[0,0,k*(x-y),f*(x-y)],[d*y,e*x,f*(x-y),m*x+n*y]], total-entry sum zero eliminates m=-i-k-2e-2f,n=-g+k-2d+2f. The three quadratic plus four cubic permanent-level coefficients imply the quartic coefficients automatically (exact remainder zero). Exact saturation overQ in all eight charts choosing a nonzero entry from each pair(g,d),(i,e),(k,f) proves only the ordinary star2 survives: g=i=k=0,d=f,e=-f, hence m=n=0. Seven charts give unit ideal; all-edge chart GB contains g,i,k,(d-f)^2,(e+f)^2.

A direct algebra proof is available. With q0,q1,q2 the half-normalized quadratic coefficients and c0..c3 the cubic coefficients in descending x-degree: d=0 gives g^3=c3-g*q2=0; e=0 gives i^3=c0-i*q0=0; f=0 gives k^3=c0-k*q0=0. Thus nonzero leaf-row pairs imply all edges nonzero. A degree6 ideal certificate proves e^2*f^3*i=0; leaf permutations give g=k=0 as well. The remaining q0,q2 are (e+f)^2 and(d-f)^2.

LEAN CHECKED: `ArrowheadCertificate.lean` proves the degree6 consequence directly using linear_combination from seven coefficient equalities; first build exited0 with empty stdout/stderr, saved as arrowhead-certificate-lean.log. The exact rational certificate was generated in6.7s using reduction modulo the three quadrics and a152-column linear solve, independently expanded to verify identity. Full classification is written in ArrowheadAlgebra.lean and was submitted for a separate Lean check; its status is pending at the time of this note. All source/equations/full diagnostic logs are archived algebra-collinear-arrowhead-* and algebra-arrowhead-*.

Both exact scoped/narrow-import ArrowheadCertificate.lean and full ArrowheadAlgebra.lean now passed Lean with exit0. Logs are arrowhead-certificate-scoped-lean.log and arrowhead-full-scoped-lean.log. The only diagnostic is a deprecation warning advising Mathlib.Basic.Complex.Basic instead of the compatibility import Mathlib.Data.Complex.Basic; there are no proof errors. All options are now declaration-scoped via `in`.

### 10:44 UTC — three_plane_search: frame and certificate review

- Both four-frame saturated ideals remain unit modulo 97 after omitting all quartic equations. Each now has sixteen quadratic/cubic equations plus saturation (566 terms). Characteristic-zero attempts remain inconclusive under the 120-second cap.
- The four-kernel stratification does not strictly require proving all kernels one-dimensional: after excluding directions with two zero rows, distinct zero-row kernel subspaces intersect trivially. At most one can have dimension two, and a generic point in that projective line avoids the finitely many joins of the other three points.
- Independently reviewed and reran the centered-two-plane exact verifier for both mixed charts. The original polynomial identities and independently reconstructed Hadamard invariants passed for chart 2 (3854 weights, 1064-bit positive constant) and chart 3 (3578 weights, 890-bit positive constant). These remain arithmetic certificates pending Lean verification and coverage formalization.

- Four-frame q+c rational saturated charts both reached the 120-second cap without a verdict. Final logs and summaries are archived. No characteristic-zero obstruction is being claimed from these finite-field computations.

## Root coverage plan / 2026-11-25T10:49:50.775412+00:00

The target remains unresolved. Main plan: homogenize L to W=span(J,L), dim4, permanent=24 times a fourth power. If some row-difference map φ_i(T)=(T_ij−T_ii) has rank3, fresh_geometry is parametrizing the top-row chart via six pure-block ratios and cubic-gradient rank conditions; its earlier bounded261-equation mod97F4 had no verdict. If allφ_i are singular, their kernels are zero-row directions (a nonzero constant row would make J−T/c have zero row). Distinct kernel points split into a frame (two saturated chart exclusions modulo97; noQQcertificateyet), exactlythreecollinear (ArrowheadAlgebra checked; actualmatrixbridge running), andallcollinear (diagonalobstruction checked). Coincidentkernelpoints need additional coverage; the fullsupport2 extension obstruction remainsCAS/projective-specialization reasoning, notLean. Three_plane is trying homogeneous edge-product certificates toavoid an inverse variable in framecharts. Centered2 chart identities areexactQQand independentlyverified, butlargeLean attempts failedmemorycaps; these are auxiliaryCASresults andnot the target.

### 10:50 UTC — three_plane_search: checked mixed-minor coverage core

- `MixedMinorCoverage.lean` compiled with exit zero and an empty compiler log. It proves that rows with zero determinant against a common nonzero row have zero determinant with each other; consequently, vanishing mixed D/O minors and a nonzero row in each block force all within-block minors to vanish. The source has 39 lines and uses narrow Complex and LinearCombination imports.
- The four-frame degree-six saturated Macaulay trial completed in 70.15 seconds with rank 10197 and no target-unit witness (12194 rows, 12376 columns). A smaller ten-variable trial now removes the saturation variable and targets `(c02*c12)^3` directly, with 8866 rows and 8008 columns.

CollinearArrowhead.lean is now Lean-checked with exit0 and empty stdout/stderr (22.67s, peak summedRSS3,853,778,944bytes). It upgrades the scalar coefficient classification to actual symmetric4x4 matrices: A row0=0, B row1=0, A+B row2=0, all permanent(J+xA+yB)=24, and each leaf row nonzero imply existence of f≠0 with A=star3(0,-f), B=star3(f,0). All coefficient equalities are derived internally from finite permanent evaluations; no additional algebra hypotheses are assumed. Log/status saved beside source.

CollinearArrowheadMaximal.lean now also passed Lean, exit0,22.65s, peak summedRSS4,226,121,728bytes under4GiBcap. It copies the checked ordinary StarMaximal lemmas, transfers maximality tocenter3 by simultaneous index swap, and proves `three_collinear_zero_rows_third_in_span`: under the actual symmetric/constant-permanent/three-collinear-zero-row hypotheses, any third compatible symmetric matrixC equals x*A+y*B. Thus this complete boundary configuration cannot occur in a3dimensional constant-level space. The only diagnostics are two unused trailing ring-tactic warnings; no proof errors. Complete build log/status archived beside source.

TwoBlockAlgebra.lean is Lean-checked, exit0,4.02s,peakRSS2,710,142,976bytes, empty diagnostics. It proves that the four symmetry-adapted quadrics plus the ordinary cubic permanent coefficient force all four extension parameters t,x,y,z to zero for every complex h withh^2=2. The quadrics alone leave six projective directions, so they do not suffice. The cubic proof is elementary: split z=±y; ify≠0 reduce tot=-3y∓2hx, Q=-20x^2∓12hxy+3y^2, xR=x(8x^2±4hxy-5y^2). Ifx≠0, 5Q+3R forces19x±12hy=0, and a short squared identity gives265x^2=0. No quartic or large Groebner certificate is used in Lean. Exact adapted matrix/coefficients and full CAS/build logs are archived as two-block-*.

### 11:02 UTC — three_plane_search: degree-seven frame targets

- The inverse-free normalized four-frame q+c ideal has a 170-element Groebner basis modulo 97 (0.77 seconds). The original homogeneous ideal has 1072 basis elements. A small C++ homogeneous normal-form implementation checked all positive edge-product exponent patterns through degree seven. No triangle or path product of degree at most six belongs to the modular ideal.
- Degree-seven members include `u01^3*u02^2*u12^2` and `u01*u12^3*u23^3`. Triangle exponent patterns are permutations of (3,3,1) and (3,2,2); path patterns have middle-edge exponent three and endpoint exponents summing to four. These are modular membership findings, not rational or Lean certificates.
- A degree-seven Macaulay matrix has 28028 rows and 19448 columns. Grevlex/leading-column row sorting was slow (4800 rows in 120 seconds); the original normalized order reached 11600 rows in 30 seconds and is now in a bounded 120-second rerun. Once a first witness is found, the plan is to prune to its nonzero source rows before CRT.

TwoBlockMatrixCompact.lean Lean passes 10.05s, peak 3.56GB. One permanent-expansion identity replaces twenty expanded evaluations; normalized block extensions vanish by the checked scalar certificate. General-C gauge and first-order normalization bridge in progress.

### Final long rowgraph F4 status 2026-11-25T11:05:12.514870+00:00

Root requested stop to reallocate computation to smaller geometric models. SIGUSR2 at11:04:47.595UTC was honored at stable round23; process exited0 at11:05:12.515UTC. The result is explicitlyPARTIAL, is_groebner_basis=false, no unit/nonunit verdict. Totalwall35.43min,CPU42.25min,observedpeakRSS4271048KiB/VM4949440KiB. Computation remaineddegree8,15800internalpolynomials/178299673terms; finalcheckpoint retains1834completepolynomials/3103152terms,53847170textbytes. The alreadyfrozen/pushedround15archive remains immutable; finalrunlog,status,result and manualstoprecord are now archivedbesideit. Latestround23gzip staysinscratch for optionalfuturefreeze. No restart without a new strategy.

TwoBlockMaximal.lean fully Lean-checked (exit0,11.08s,3.718GB): for h²=2, any symmetric C with permanent(J+UA(h)+VB(h)+WC)=24 lies in span(A(h),B(h)), where A/B are the disjoint normalized 2×2 support blocks. First-order conditions and arbitrary-C gauge are derived internally; no extra coefficient assumptions. Root notified for review/push.

TwoDoubleKernel.lean Lean PASS, exit0,10.04s,3.791GB. Final theorem two_double_kernel_rows_maximal: arbitrary symmetric nonzero A,B with A rows2/3 zero and B rows0/1 zero, symmetric C, all permanent(J+UA+VB+WC)=24 imply C∈span(A,B). This includes support classification, complex square-root normalization, permutation, and arbitrary-C compatibility internally. Source is396lines25.6KB; no unresolved goals. Full logs/status beside source.

OverlapBlocks.lean Lean PASS, exit0,4.02s,3.26GB. Final overlap_zero_rows_impossible: two symmetric nonzero level directions with A rows2/3 zero and B rows1/3 zero cannot coexist in a constant-permanent linear family. Includes scalar root certificate giving7=0, block classification, actual permanent coefficient extraction, rescaling, and raw row support conversion. This excludes two support2 directions whose supports share one vertex.

## 2026-11-25T11:12:42.365658+00:00 geometry_route: all four Sym3 chart certificates checked

All four finite three-parameter Witt-chart cubic obstructions Sym3Chart00/01/10/11 compile in Lean, with exact integer linear-combination certificates at Macaulay degree14. Sources are37–45KB, multipliers420/363/369/398 terms, denominator sizes91/61/66/48bits. All four source identities independently reviewed (00 rules_review;01/10/11 fresh_geometry). Exact source, input metadata, sparse matrix, integer witness, full Lean logs/status, and independent reviews are archived under results/orch/lemmas. These are scoped chart obstructions; the formal chart coverage and actual symmetric3×3-supported matrix bridge remain unfinished. No global L-gct-231 conclusion follows yet.

The full top-row chart's exceptional case in which each complementary diagonal form vanishes on its coordinate pair has a reported rational Gröbner basis `[1]`. The hafnian term `H=Σ t_i Cjk` is one signed square multiple of `ℓ²` on all three pairs. Tangency reduces the remaining coefficients to six unknowns plus `h²=24`. Rational F4 returned `[1]` for 20 equations in 37.70 seconds. Derivation and reproducible inputs/results are in `lemmas/fresh_top_allzero.md` and adjacent files. Independent verification of the rational unit identity and a Lean certificate are pending. The complementary branch has a binary pair with nonzero `D`.

### 11:14 UTC — three_plane_search: reviewed checkpoint extraction

- A separate checkpoint-capable copy of the reviewed modular Macaulay solver passed four resume-equivalence tests (5–22 chunks), independent modular identities, and matrix/prime/provenance mismatch rejections. Atomic snapshots include all pivots and dependency data and bind SHA-256 hashes of the matrix and provenance metadata. The original solver is unchanged.
- rules_review approved the source, wrapper, and tests after explicit ordinary child environments, disabled core dumps, and streaming SHA hashing were added. Approved sources and test output are archived here.
- Root renewed the lease at 11:10:45 UTC (expiry 11:30:45 UTC). The authorized 600-second, two-GiB first-prime extraction started at 11:14:15 UTC and writes atomic checkpoints roughly every minute. A separate verifier already reconstructed all sixteen source equations from the permanent; it will verify and prune any resulting modular witness.

RowKernelScaffold.lean Lean PASS, exit0,3.52s,3.27GB, empty diagnostics. On a constant-permanent submodule, any constant row of a direction is zero; proof scales it to a zero row and uses permanent=0 versus24. Defines rowDifference L i using column0 as reference and columns1..3 as differences. Its kernel equals the zero-row directions. For finrank L=3, a nonsurjective row-difference map yields a nonzero zero-row direction; row_dichotomy gives either a bijective row chart or a nonzero zero-row direction. If all four maps are singular, zero_row_directions_of_singular_rows chooses four nonzero directions with the corresponding zero rows. No symmetry assumption is needed.

## Exact projective zero-row configuration cover (construction_algebra)

Choose arbitrary nonzero directions v_i in L with row i zero, for i=0,1,2,3. Their projective classes give a finite exhaustive list:

1. A class appearing at least three times: its representative has at least three zero rows. Symmetry leaves at most one diagonal entry; the linear permanent coefficient forces that entry zero, contradiction. This covers multiplicities4 and3+1.
2. Exactly two classes, each appearing twice: disjoint support-two directions. TwoDoubleKernel excludes an independent third member of L.
3. Exactly three classes (multiplicity2+1+1): either their representatives are independent (the repeated-kernel basis chart), or dependent with all three projective classes distinct (three-collinear arrowhead case).
4. Four distinct classes: if any triple is dependent, use the three-collinear arrowhead case; otherwise every triple is independent and the fourth has three nonzero coefficients in a basis formed by the first three, giving the four-frame chart.

There is no separate all-four-collinear case: it is included in item4 with a dependent triple. A three-collinear triple can be normalized to A,B,A+B by rescaling the nonzero relation coefficients; distinctness makes all relation coefficients nonzero. The leaf-row nonzero conditions in the checked arrowhead theorem follow from OverlapBlocks: if, for example, B also has row0 zero, then B has rows0/1 zero and A+B has rows0/2 zero, giving two nonzero support-two directions sharing one vertex. The analogous arguments handle A row1 and A row2. Thus no nonzero leaf hypothesis is a genuine omitted geometric case.

This classification does not require the row-kernel subspaces to be one-dimensional or a generic choice of points. It classifies any chosen four nonzero representatives. To turn it into the global Lean proof still requires: the rank-three repeated-kernel chart obstruction, the four-frame chart obstruction, permutation transport, finite projective equality/dependence case splits, and converting the resulting span bound to finrank≤2. Current mathematical/CAS or partial chart results must not be treated as checked global coverage.

CollinearLeafConditions.lean Lean PASS, exit0,8.07s,3.27GB. Given nonzero symmetric A,B,A+B, rows A0=0,B1=0,(A+B)2=0, and constant permanent for their plane, proves exactly the three nonzero-leaf-row assumptions required by CollinearArrowheadMaximal. Uses OverlapBlocks with three explicit simultaneous row/column permutations; the degenerate leaf cases are fully excluded.

ProjectiveNormalization.lean Lean PASS, exit0,3.52s,3.24GB, empty diagnostics. Generic helpers: collinear point outside either singleton span has two nonzero relation coefficients; in a3-dimensional complex space, four vectors with every triple independent have three nonzero coefficients for the fourth in the first-three basis; any submodule contained in the span of two vectors has finrank≤2, hence cannot have finrank3. This supplies normalized arrowhead/frame coordinates and the final dimension contradiction, not the full finite configuration case split.

DependentTripleNormalization.lean Lean PASS, exit0,2.51s,2.92GB, empty diagnostics. Pairwise independent A,B,D with dependent triple D,A,B have D=aA+bB with both coefficients nonzero. Also proves finite independent families remain independent under pointwise nonzero scaling.

RowChartScaffold.lean Lean PASS, exit0,3.52s,3.24GB, empty diagnostics. Extends RowKernelScaffold: a surjective row-difference map on dim3 L provides an injective linear parametrization F:(Fin3→C)→ambient with range exactly L and normalized row differences F(x)_(i,j+1)−F(x)_(i,0)=x_j. Together with the singular case, both sides of the global row-chart dichotomy now have checked linear-algebra realizations.

### 11:24 UTC — three_plane_search: first bounded extraction preserved

- The first reviewed checkpointed extraction ended at its time budget. Saved state: next row 21654, rank 17166, 512417332 checkpoint bytes; complete run records and full diagnostics are archived. No witness was produced in this interval.
- Both degree-seven monomial memberships were independently reconfirmed at the extraction prime 1000000007 using homogeneous F4 and direct normal-form reduction. The read-only checkpoint query utility was independently approved and passed twenty tests; neither target was in the earlier saved prefix at row 19697.

## 2026-11-25T11:26:46.451164+00:00 geometry_route: full Sym3 zero-row dependence theorem checked

Sym3ZeroRowDependent.lean (SHA e52d94517d5d199d0df2c498f33d31ff67d684e657d2b3765ab3e58403956376) compiles exit0 in146.42s. It combines all four integer chart certificates, formal four-chart coverage, inverse-minor basis normalization, exact cubic extraction, actual matrix decoding, and arbitrary-row permutation. Final theorem same_zero_row_pair_dependent: symmetric A,B with a common zero row, A nonzero, and permanent(J+aA+bB)=24 for all a,b imply B=cA. There are no external coordinate/coefficient assumptions. Thus a constant-permanent symmetric subspace has at most one projective direction with any given zero row. This remains a partial result for L-gct-231; the general three-plane exclusion is not claimed. Source866lines191585bytes; full compiler log/status archived, independent review requested.

For the binary full-row chart with `D` and `ℓ` proportional, the root `D=0` is a permanent-singular level direction. When its 2×2 cross block is invertible, all complementary 2×2 entries vanish there. A five-parameter parity reduction gives six level equations. Rational F4 after adjoining `h²=24` and saturating the nonzero `E=d+e` returned `[1]` in 101.52s. The input and direct symbolic coefficient verification are archived with `lemmas/fresh_top_dependent_cross.md`. Independent unit-identity verification and Lean checking remain pending. The case of a vanishing cross row reduces to the established supported-Sym3 obstruction or four fixed rank-three directions.

### 11:30 UTC — three_plane_search: checked four-frame support coverage

- `FourFrameCoverage.lean` compiled with exit zero and an empty compiler log (3.52 seconds). Six zero/nonzero cases show that vanishing of all sixteen independent edge-triple products forces support in one of four stars or three matchings. A second theorem supplies the corresponding explicit nonzero vector annihilating the six off-diagonal forms.
- This is a coverage lemma conditional on the triangle/path products vanishing; the required characteristic-zero algebraic obstruction is still being extracted.

2026-11-25T11:32:47.801391+00:00 construction_search: DoubleSingleMatrixBridge.lean is Lean-checked (exit0,13.21s,peak2.51GiB). It proves the generic repeated-zero-row actual permanent expansion modulo rr^2=2 and extracts all19 coefficients by a verified19-point interpolation inverse. This connects actual matrices to coefficients, without claiming global kernel coverage. Source/log/model archived; full certificate-wrapper integration is compiling next.

FourDirectionCover.lean is now Lean-checked: complete generic projective case cover, including explicit collision-pair permutation and LI-pair/singleton-span equivalence. GlobalCoverConditional.lean combines it with the checked row dichotomy and proves the exact negation of the posted existential from six explicit branch obstructions. ConcreteTripleCollision.lean discharges triple coincidences from actual level/symmetry hypotheses. ConcreteDoubleCollision.lean discharges2+2 via TwoDoubleKernel and the finrank≤2 wrapper. ThreeBranchGlobalCover.lean combines these with the actual arrowhead/automatic-leaf lemmas and is prepared to leave only full-row,repeated-independent,frame inputs; its first full compile is waiting for the root-authorized6GiB slot after construction_search. No unconditional refutation is claimed.

## Root re-plan at 2026-11-25 11:37 UTC

The posted target remains unresolved. All checked results are partial, except full local obstructions explicitly stated in their files. No target checker/PR has been run. Root is preserving every reviewed checked file on pnp/pilot-79.

Current division: algebra integrates the exact posted negation with concrete triple, double-pair and collinear exclusions, leaving full-row/repeated/frame hypotheses; construction_search combines actual repeated-kernel matrix bridges and inverse scaling with both certificates; geometry has completed the full same-zero-row proportionality theorem and is certifying both fixed exceptional directions; fresh handles the generic principal-block chart and remaining pivot coverage; three_plane resumes the degree7 four-frame matrix with complete atomic checkpoints; rules independently reviews every checked source and archive. Root handles the all-zero binary-diagonal chart and publishing.

All-zero chart: an independently verified exact2501-term unit identity exists, with421-bit positive constant. Direct215KB Lean source exceeded4GiB and8GiB RSS caps. S3 averaging provides a378-term weighted input combination whose normalized polynomialF has1821 nonzero terms and whose six images sum to the constant. New309KB split source uses short integer linear combinations of378 baseweights for its intermediate coefficients. Root will compile it after the combined repeated and integrated-global6GiB jobs. No allzero Lean verdict yet.

Four-frame: first600-second window preserved row21654/rank17166; second resumed at11:25:13. Both degree7 targets are independently in the full ideal component at the actual prime1000000007; full relevant row-space rank18860. Neither was in the saved span at row23697/rank17998. This is finite-field evidence; rational reconstruction and Lean certificate remain required.

Source-size cap512KiB remains a material integration concern. Eliminate duplicate helper bodies and unused Sym3 classification if the final route does not need it; consider Horner forms for certificates. Do not relax the posted statement or claim a global refutation from conditional/CAS evidence.

2026-11-25T11:37:19.034851+00:00 construction_search: DoubleSingleMatrixFull.lean is Lean-checked (exit0,164.48s,peak5.153GiB). Both actual normalized repeated-zero-row models are impossible (e=f=1 and i=f=1), with inverse-coordinate-scaling corollaries for arbitrary e≠0,f≠0 and arbitrary i≠0,f≠0. Full source includes both checked polynomial certificates and the checked actual permanent coefficient bridge. This is not yet the geometric theorem reducing every repeated-row kernel arrangement to these models. Full source/log/metadata archived for immediate independent review and push.

ThreeBranchGlobalCover.lean FULL COMBINED LEAN PASS, exit0,24.66s,peak4,938,936,320bytes,1841lines101KB. Final refutation_of_three_geometric_obstructions concludes exactly the negation of the posted gap from ONLY three explicit geometric inputs: nonsingular-row chart, repeated-independent zero-row chart, and four-frame chart. Every other branch is concretely discharged inside the same checked file: constant-row argument, row-map dichotomy, complete projective finite cover, triple coincidence, arbitrary2+2 via TwoDoubleKernel, and arbitrary three-collinear via scalar normalization, permutation, automatic leaf conditions, ArrowheadMaximal, and finrank≤2. The three remaining inputs are genuine outstanding obligations; this is not an unconditional refutation. Root informed for immediate independent review/push.

## 2026-11-25T11:40:21.442577+00:00 geometry_route: exceptional fixed-direction branches

For r⁴−4r³+14r²−4r+1=0, α=−2(1+r)/(1−r)², consider T supported on indices0,1,2 with block[[0,1,r],[1,α,−αr],[r,−αr,αr²]]. Its permanental cofactor matrix is exactly[[-(r+1)²,0,0],[0,r²,r],[0,r,1]]. A canonical partner with top-row differences(0,1,0) can be written N_B−a_B J, with N_B top row(0,0,1,0), six lower variables, and a_B=(sum lower+2)/16. Eight coefficients of per(J+tT+xB)−24 are archived in geometry-exceptional-raw.json. They imply the exact factor identity f22−(b5−a_B)f21=(r*b2+b4)*(r*b2+b4−2(r+1)b5). In either branch, two fixed-T linear coefficients plus the branch solve three variables, leaving three extension variables and five equations. Both ideals plus r quartic have QQ Groebner basis[1] in0.13/0.16s.

Quotient-Macaulay degree5 gives224columns/256rows and integer witnesses; full six-polynomial identities include explicit quartic correction. ExceptionalPlusCertificate.lean and ExceptionalMinusCertificate.lean are Lean-checked and independently reviewed, constants183/296bits. Source92/114KB, compile36s each. These are polynomial obstructions only so far. ExceptionalRawReduction.lean now compiles the branch and pivot bridge (active); ExceptionalCoefficientBridge.lean is generated but untested. Full actual fixed-direction theorem remains unfinished. Fresh independently verified all model coefficients, cofactor entries, and pivots.

MatrixChartAdapters.lean Lean PASS, exit0,4.02s,3.34GB. Defines exact actual-matrix interfaces RepeatedMatrixObstruction (A rows0/1 zero,B row2zero,C row3zero,independent) and FrameMatrixObstruction (A row0zero,B row1zero,C row2zero,A+B+C row3zero,independent), each assuming symmetry and the permanent family. Checked adapters turn these interfaces into the corresponding remaining abstract inputs of ThreeBranchGlobalCover, including projective collision row transfer/permutation/independence transport and choosing a basis insideL/rescaling nonzero frame coefficients. No additional geometric assumptions remain in these adapters.

### 11:42 UTC — three_plane_search: verified first modular frame witness

- The triangle witness was found at rank 18538 with 17549 nonzero original-source row weights. The complete matrix identity and direct original-polynomial identity were independently checked modulo 1000000007, and the original sixteen q/c equations were independently reconstructed from the permanent. The witness and full run diagnostics are archived.
- Pruning yields 17549 rows and 18570 columns, too large for efficient repeated-prime elimination or a compact final Lean source. Root assigned construction_algebra an iterative low-degree closure/DAG route. I am preserving final pivots for p-adic lifting with a separately reviewed replay variant; every reconstructed rational result will still require a complete exact integer identity and Lean verification.

Four-frame low-degree DAG route: exact finite-field row reduction at primes97 and1000000007 gives identical rank data. D4:506rows,1001columns,rank491,retained≤3 rank76 (6quadratic+70cubic), which equals the original D3 space. D5:2376rows,3003columns,rank2151,retained≤4 rank491, exactly original D4 space. Therefore repeated retention/multiplication at D4/D5 adds no new consequence and cannot shorten the certificates by this proposed method. Triangle target has a nonzero remainder. Diagnostic source/fulllogs/status archived as frame_lowdegree_closure.py and frame-lowclosure-*. No rational/Lean certificate is claimed.

2026-11-25T11:48:42.679368+00:00 construction_search: DoubleSingleGeometric.lean passed Lean (exit0,32.00s,peak2.64GiB). It includes the full arbitrary-A repeated-row matrix reduction, with explicit ModelImpossible and DisjointMaximal callback conclusions, plus the finite swap0/1 proof reducing ModelImpossible to the checked same/cross inverse-scaling theorems. All hard geometric steps are checked; the336626-byte composition with both actual certificate proofs and the actual disjoint-block theorem awaits one final compile. This does not yet refute the full posted gap.

2026-11-25T11:52:37.768922+00:00 construction_search: COMPLETE repeated zero-row branch is Lean-checked. DoubleSingleComplete.lean (1313lines,336626bytes) passed exit0 in193.42s,peak5.666GiB. The final actual_repeated_matrix_obstruction has no callback hypotheses and exactly matches MatrixChartAdapters.RepeatedMatrixObstruction: arbitrary symmetric independent A/B/C, A rows0/1zero,B row2zero,C row3zero, all constant-permanent combinations impossible. All proof dependencies included. Source and full profile/diagnostics archived for immediate independent review and push. This does not by itself settle the full posted gap.

### Four-frame modular D6 closure — 2026-11-25T11:57:20.512123+00:00

The reviewed checkpoint backend completed all 8,866 meaningful degree-six Macaulay rows at p=1,000,000,007 with rank 7,191 in 68.63 s (peak 151 MB). Stable row ordering processed all degree-at-most-five source rows first. The independently reviewed exporter found **247 new lower-degree consequences: 67 quartics and 180 quintics**, increasing the low-degree span from 2,151 to 2,398. Every exported row was reconstructed from original matrix rows and checked modulo p, with checkpoint/matrix/metadata SHA bindings and explicit sentinel rejection. Export took 22.24 s. These are modular diagnostic identities, not yet rational or Lean certificates. Sources, complete logs, status and compressed consequence/provenance data are archived in `results/orch/lemmas/frame-d6-*`. Continuation prioritizes new quartic multiples to seek additional degree falls and a smaller certificate DAG.

2026-11-25T11:59:12.087114+00:00 three_plane_search: Continue-all checkpoint variant and Dixon lifting engine/runtime/tests independently approved by rules_review. Continue-all handles an already-restored unit pivot, preserves seed checkpoint, final-saves complete state, and tests uninterrupted/chunked/resumed coordinate witnesses. Dixon small tests check exact integer carry at every digit, independent rational solutions, rectangular/inconsistent cases, overflow guards, state binding, and poisoned-state rejection. Production continuation/lifting awaits root resource and fresh-lease authorization. These are tool validations, not a new frame certificate or Lean proof. Sources and test logs archived under results/orch/lemmas/three_plane_*.

### Four-frame D6 closure reaches both targets — 2026-11-25T12:01:02.550026+00:00

The reviewed prioritized continuation terminated successfully after 86.33 s: rank 7,683, 492 new pivot nodes, 331 degree falls, 4,050 processed multiples. Both triangle `u02^2*u12^2` and path `u12^3*u23^3` reduce to zero. The triangle is exactly one pivot (index 7,629); path reduction uses 5,667 pivots. Every continuation edge was independently replayed modulo 1,000,000,007, and all resumed-node validation was independently reviewed. This remains modular evidence, not a rational or Lean certificate. Source, complete log, status and 5.23 MB compressed DAG are archived in `results/orch/lemmas/frame-d6-continuation*`. The triangle target column is last in the Macaulay ordering, so many nominal quartics have cubic leading terms with the triangle as their sole degree-four tail; removing that now-known zero should expose small cubic intermediates.

2026-11-25T12:05:59.914820+00:00 three_plane_search: Reviewed continuation found the path monomial u12^3*u23^3 at prime1000000007 after114.46s, next_row25945, rank18691, witness support17569; peak758542336bytes. Both the full Macaulay matrix identity and independently parsed original16 q/c polynomial identity were verified. Immutable triangle seed unchanged; separate complete path basis snapshot preserved in scratch. Modular witness and complete run diagnostics archived under three_plane_*. This is finite-field evidence, not a characteristic-zero or Lean certificate.

### Four-frame small cubic candidates — 2026-11-25T12:06:03.680965+00:00

The independently reviewed low-row back-reduction returned 177 cubic rows and six quadratics after removing the isolated triangle tail. Reconstructing coefficients at p=1,000,000,007 and independently reducing the resulting rational candidates modulo97 accepted32 rows (644 terms), rejecting151. Two small candidates are `u02*(a*g - 8*(u02+u03)*(u12+u13))` and `u02*(a^2 + 8*a*(u02+u03) + 8*(u02+u03)^2)`. They suggest a root-choice/odd-cycle argument, but their characteristic-zero ideal membership is NOT established. The exact membership proof remains necessary. Raw dependency pruning still uses7,558 pivots for triangle and7,585 for path, so simply retaining the full modular DAG is not yet a compact proof. The large-prime affine GB was also computed in under1s; most of its nonquadratic coefficients do not reconstruct within the one-prime bound. All diagnostic sources, full logs, inputs hashes, reduced rows and candidate factorizations are archived in `results/orch/lemmas/frame-d6-*`.

2026-11-25T12:11:27.583241+00:00 construction_search: Major repeated-case compression. Same handles overlapping nonzero supports of B crossvector (f,j) and C crossvector (e,i), directly when f,e≠0 and after swapping0/1 when j,i≠0. The only remaining orientation has e=j=0 and f,i≠0. Its normalized f=i=1 case is Lean-checked in DoubleSingleSparseCross.lean using only five actual coefficient equations: after g/k elimination, h4-h2-h7-8*hr gives20=0. This removes the general Cross certificate entirely. Separately, Same quotient/Horner certificate is Lean-checked (82778bytes,25.36s,2.61GiB), retaining every original hypothesis. Complete compressed composition candidate is169702bytes versus authoritative336626; finite support case split/final composition await the next resource slot.

2026-11-25T12:14:20.931229+00:00 ROOT REPLAN: Exact target still unresolved. Repeated branch complete checked at336626bytes; checked Same quotient plus sparse Cross reduce candidate composition to169702bytes, pending final composition check. TopAllZeroObstruction20-polynomial implication passed Lean281.74s/9.89GB and is pushed; actual geometric/sign-gluing bridge remains. Frame triangle/path modular witnesses verified; triangle Dixon202digits/6040bits still unreconstructed, so compact two-cubic identities and eight paired-root sign cases now prioritized. Geometry raw exceptional Horner uses exclusive11GiB/300s; abstract integer-identity fallback prepared. Fresh focuses physical full-row alliso chart, larger bounded run authorized after memory slot clears. Root sparse scalar wrapper is checked/reviewed/pushed; paired-row affine plane and frame paired roots prepared for next small Lean slot. Latest pushedHEAD700d0ba9. No target checker or PR.

2026-11-25T12:14:43.953717+00:00 three_plane_search: Triangle Dixon lift finished298.85s at202digits/6040bits, all exact carry identities checked; only4nonzero reconstructed fractions stable, so no rational certificate. Cross7616 and square7618 candidates both pass2digits/60bits against saved degree7 basis (7.24s/5.74s); generic witnesses remain~17.6k support. GMP reconstruction and ordered-variable polynomial-RHS drivers independently reviewed, small tests pass. Candidate full19eq lowdegree certificates now take priority with construction_algebra. All states/logs preserved; triangle202 state compressed separately to avoid changing earlier approved snapshots.

2026-11-25T12:18:25.542367+00:00 construction_search: DoubleSingleCompactComplete.lean is now fully Lean-checked: exit0,116.68s,peak3.973GiB,169702bytes/1165lines. It proves exactly the same unconditional repeated-row matrix obstruction as the preserved336626byte file, including every certificate/geometric dependency. The finite support split and sparse Cross scaling are checked. Archived complete source/profile/metadata; final independent composition review requested for immediate push. Moving to sparse-star geometric normalization as root assigned.

### Lean-checked four paired-root cases — 2026-11-25T12:20:13.962369+00:00

`FramePairedCases.lean` passed Lean, exit0 in16.64s, peak3.520GB, emptylog; SHA4bb780f0222f807cedbfe3b0581da4a7d6a84f35fea0593ee4a0bb5493735b33. It proves all four relative-root cases impossible using exact degree-four integer identities (59,703bytes). Three_plane independently reconstructed the original6quadratics from all24 permanent permutations and verified each substitution and identity separately overQQ[r]/(r²−2). This establishes only the conditional algebra: the six norms and three cross-products still need derivation from actual frame constraints. Their two tiny base cubics are not in the full19-equation Macaulay span at degree4,5,or6 (ranks494,2184,7371); full19 degree7 input with low-degree/short-row ordering has been generated to seek smaller exact certificates. The scalar paired-root bridge is compiling as `FramePairedTriangle.lean`.

### geometry_route exceptional direction status 2026-11-25T12:22:28.384781+00:00

Both scalar branch certificates, the complete raw-eight-equation reduction, and the actual permanent/coefficient/partner-normalization bridge are now Lean-checked and independently reviewed. Raw Horner reduction passed in296.10s at9.289GB peak; actual coefficient bridge passed in92.56s at5.381GB. The remaining composition is prepared as scratch ExceptionalFixedDirection.lean (385937bytes), queued for one exclusive11GiB/600s check. Its intended endpoint excludes a symmetric partner with row0 differences(0,1,0) for the fixed zero-row direction T(r), where r^4-4r^3+14r^2-4r+1=0. This is a local exceptional-direction obstruction, not a global refutation.

A generic-integer normalization optimization has one checked identity, but the full identity file exceeded4GiB; the established checked Complex route remains primary. All complete logs and exact certificate/model data are archived under results/orch/lemmas.

2026-11-25T12:26:29.859440+00:00 three_plane_search: Full19 normalized frame source independently checked against all24-permutation permanent coefficients (6q,10c,3quartics). Lowdegree/nnz ordered D7 cross-target matrix generation and new checkpoint runner independently reviewed. Authorized300s/2GiB extraction running, session39226: after138s next_row23918/rank17941/peak216592384bytes. Matrix frame-tiny-full-cross-d7.matrix; metadata same stem; checkpoint -tracked.checkpoint, final basis will be -tracked.checkpoint.final. Reviewed shared-basis three_plane_full19_dixon_run.py supports cross/norm original polynomials through exact integer column transformation and final source-polynomial replay. No full19 production Dixon run yet.

2026-11-25T12:31:20.901090+00:00 three_plane_search: Ordered full19 D7 cross extraction succeeded275.18s/rank18746/peak288612352bytes,17082nonzero weights; independently replayed transformed matrix and original19polynomial identities. Norm belongs to same basis, initial21digits/628bits exact carry checked in~10s. Authorized300s norm lift now active session31013; source-bound GMP reconstruction, exact final original-polynomial verification mandatory. Ordered generator, matrixgzip, metadata, cross witness, reviewed runners/tests and an immutable precision141 norm-state snapshot archived in three-plane-ordered-full19-archive-manifest.json. Still no rational base certificate.

### Conditional paired-path scalar cases checked — 2026-11-25T12:36:05.846877+00:00

`FramePathPairedCases.lean` passed exit0 in4.54s,peak2.716GB,emptylog. Four degree-two identities use ten terms each and≤13bit rational coefficients. Source is3,938bytes. Three_plane independently verified all root/chord substitutions and exact field identities. This is a conditional fallback path component; base frame norm/cross consequences remain unproved. Norm-only modular tests now suffice for triangle, and for path after triangle excludes both chords, so the main route prioritizes the single norm base cubic. Ten norm-only triangle representatives have exact degree-four unit certificates; the64-pattern S3/globalconjugation adapter and homogeneous Lean certificates are being prepared.

2026-11-25 12:36 UTC — construction_search: SparseStarSubmoduleComplete.lean PASSED pinned Lean (60.01s,2.724GiB RSS). Unconditional actual independent-triple and rank3 matrix-submodule obstruction for the sparse star with edges (1,-1,0), including finite-sample polar extraction and gauge/affine-plane classification. Research partial only; no global gap claim. Source and complete logs archived; independent review requested before parent push.

2026-11-25T12:37:13.935274+00:00 three_plane_search: Final ordered norm fixed-basis lift reached361digits/10793bits, all exact carry identities verified, zero stable nonzero fractions and6685 unreconstructed coefficients. Actual318.07s exceeded requested300s because final reconstruction/verification finished after child deadline; future runner now reserves postprocessing time (review pending). Fixed-basis lifting stopped as impractical for source size. Final state/run/step and actual timing archived in three-plane-ordered-norm-final-archive-manifest.json. No CAS or Lean jobs active; geometry has exclusive13GiB window.

2026-11-25T12:41:13.707333+00:00 ROOT REPLAN: repeated branch complete in169702bytes; sparse-star rank3 matrix obstruction newly checked/reviewed (awaiting push); allzero sign glue/skew/matrix coefficient bridge checked/pushed, explicit-model composition332878Bqueued; genericDzerochartnormalization17435Bprepared. Conditionaltriangle/pathcases checked, norm-only10orbitcerts exact butbasecubicstillunproved. FixedbasisnormDixon10793bitsnoexactcertificate, stopliteralcertificate route. Exclusive13GiB600s exceptionalstrongendpointretry active12:36:32–12:46:32; allotherCAS/Leanpaused. Generalfullrowgenericcase remainsmain mathematicalhole. No target checker/PR.

2026-11-25 12:48 UTC — construction_search: AllZeroGeneralNormalization.lean PASSED12.82s/2.358GiB. Arbitrary all-D-zero pencil normalized to exact TopAllZeroBridge.model, with full permanent identity, using checked sign glue/skew reconstruction. Archive+manifest ready for independent review. Root will compose with its explicit model obstruction; no full gap claim.

2026-11-25 12:49 UTC — construction_search: SparseStarPairComplete.lean PASSED57.22s/2.731GiB. Exact product-coordinate ambient rank3 sparse-star obstruction with no callbacks now checked. Source+fulllogs+manifest archived, independent review requested.

2026-11-25T12:50:03.502712+00:00 three_plane_search: Exact diagonal-anchor gradient/Hessian quotient net obtained by Newton power sums and partition-Mobius averaging over all24root permutations. All exact entries match independent fresh p461 gradients, kernel coordinates, Hessians and entire35x35moment matrix. detH0=9803356117276277820358656; operators do not commute. Integer35x35moment has525nonzeros, max46bits, exact nonzero623bitdet reducing312mod461. Net computation0.11s; exactdet0.01s. Data/source/logs archived via three-plane-diagonal-anchor-archive-manifest.json. No Lean claim; all computation now paused for root large Lean.

### Dense-star concrete matrix bridge — checked 2026-11-25 13:03 UTC

`DenseStarMatrixConstraints.lean` (SHA256 `542090ab049f61c88579f77d277546a9eab0aef54bd31d1ef857fd82d8422f39`) passed direct Lean in 10.76 seconds, peak RSS 2.58 GB. For a constant-permanent symmetric family containing the normalized dense star `(1,h,-1-h)`, its explicit three linear lower-block coordinates satisfy a nondegenerate ternary quadratic. Zero coordinates force the entire matrix to be a centered star. The final submodule contradiction is being composed by construction_search from the rank/kernel lemmas and the checked sparse-star obstruction. This file is a checked local matrix bridge, not the global gap result. Fresh independently reviewed the source-aligned polynomial identities and matrix scope.

## 2026-11-25T13:30:46.428618+00:00 new hard step L-meta-3773

L-gct-231 renewal returned410 at13:07 despite the previous13:20:57 expiry; stopped old work and preserved checked partials plus explicitly unfinished diagnostics. Desk assigned L-meta-3773 at13:09. Exact goal is a63-gate monotoneAND/OR circuit for26-input projective-plane incidence with four normalized head cases. Existing L_meta_3771 proves the finite test specification is exact. All three reduction slots are already occupied, so no fourth reduction is available.

Current routes: construction_search does full-network CGP, now using68-gate exact CNF seeds with an unproductive AND gate; three_plane_search does SAT repair of the58-gate three-output24-input core; geometry_route does core CGP and64-gate Lean positive control; construction_algebra and root search four-arc replacements with free external OR gates; fresh_geometry analyzes local repair obstructions; rules_review owns packed kernel verification and independent search reviews. Generic finite checker, packed transfer, and exact witness assembler have passed Lean and independent review. There is no63-gate witness or full refutation yet. Ordinary C6, theta and K4-subdivision lower bounds already exist in the repository; only free-OR/more-global variants merit further search.

## Construction algebra, L-meta-3773, 2026-11-25 13:44 UTC

Ordinary local SAT diagnostics (not Lean proofs): C6 at seven gates UNSAT in 2.47s; C6 at eight gates with a nested AND UNSAT in 47.81s. C8 at ten gates timed out twice; K4 subdivision at fourteen gates timed out. Fresh subsequently located checked ordinary lower bounds in L_meta_723 (K4 subdivision at least15) and L_meta_615 (theta at least12), so ordinary searches stopped.

The exact helper interface is useful. Four-arc patch P={0,1,2,5}: 14 physical inputs, 15 compatible outside-star OR features, 18 local gates would give63 globally. Prefix order can begin with OR(lines9,12); affine maps p↦9p+3,l↦9l−3 then swapping sides normalize it to OR(inputs0,1). Data and compatible tree variants: scratch meta3773-full-patch-data.json. Root/reviewer independently approved the cost and input mapping. Two60s CGP runs explored roughly151million mutations; best correct local size19, best correct patch with a bad AND21. No18 witness. Fresh claims a complete semantic exclusion of the reduced K4 helper strata; independent review is pending.

The generic safe +1 nested seed does not produce a bad AND. A stronger exact +2 seed for two stars F=a(b∨U)+c(b∨V) is T=(U∨b)∧(a∨c), P=T∧(a∨b), F=P∨cV. T can be true on a negative input. This yields a66-gate full circuit, and the main CGP search is using it.

New root-priority five-point patch P={0,1,2,3,6}: one collinear triple, 11 incident lines,16 raw+16 free inputs,20 positive+30 maximal-negative samples. A23-gate local patch gives63 globally (16 freeOR+8 remainingoutsideOR+8 outsideAND+23 local+8 finalOR). All compatible trees are enumerated: six3-leaf groups have3variants each, one2-leaf group has1, one4-leaf group has15 (12chains+3balanced). Data/generator/header: scratch meta3773-five-patch-data.json, meta3773_five_patch_data.py, meta3773_five_patch_data.hpp. The uint64 CGP worker meta3773_five_patch_cgp.cpp mutates both circuit and tree choices, and independently replays any reported patch on all65536 raw assignments. No23 witness yet.

A proposed two-star eight-gate suffix with nine free crosspair ORs is impossible by a simple interface argument: all nine raw inputs remain mandatory direct leaves because the singleton-center maximal negatives dominate all helper signals. Eight binary gates allow at most nine input leaves, hence no helper is usable; the remaining raw two-star function is not read-once and needs nine gates.

## 2026-11-25 13:46 UTC — geometry route, L-meta-3773

Reduced24-input/3-output core search has no witness. Runs7901–7906 and independent scalar replay are archived in results/orch/meta3773_geometry; best58-gate candidates omit two required edges. Fresh independently approved the31-file archive. A seventh dense-overapproximation curriculum also failed and remains scratch-only. A new56-gate pencil overapproximation and two-gate contextual mutation source are prepared but paused for CPU allocation.

The exact808-row literal64-gate replay is kernel-checked in1.425s. Reviewer input-word0 and four-word probes pass; the26-word file hit300s without proof errors. The combined41.7KB positive-control source is currently checking with a600-second/6GiB bound. Its new rewrite tail separately passes. All64-gate work is explicitly a positive control and does not meet the63-gate task.

Independently reviewed the arc patch assembler baseline64, the local four-arm fanout diagnostic, and the complete augmentedK4-subdivision14-gate exclusion diagnostic. These local CAS searches have no global lower-bound or Lean-proof claim.

2026-11-25T14:14:27.862806+00:00 L-meta-3773 status: posted63bound unresolved. Complete checked64baseline and exact63conditional packed verifier are preserved on pnp/pilot-79. The library audit found only conditional64lowerbounds; NOT+Monotone2/IsAO2 assumptions in apparent flattening results are contradictory and cannot yield a general refutation. L8141 gives a genuine small-support bad-AND necessary condition. Finite local exclusions are scoped to stated star-replacement models, not the full circuit class. Root MILP attempts yielded no candidate before bounded timeouts.

2026-11-25 14:17 UTC — geometry_route: late-witness generator passed ten validation/rejection tests, then generated a complete 64-gate positive-control Lean file which passed in65.01s with4.227GB peak RSS (source888becf4…). Default generator bound remains63 and exact posted statement is pinned; no63-gate witness exists in these artifacts. Reproducible pipeline and complete logs are archived under results/orch/meta3773_witness_pipeline, awaiting final independent archive binding.


### 2026-11-25 14:23 UTC — Construction-algebra final local-search preservation

No63-gate witness or Lean refutation was found for L-meta-3773. The final two six-point CGP runs completed68,596,736 and67,600,384 mutations in90seconds each. Both retain the known29-gate local baseline (target28), with correct31-gate bad-AND patches; their nearest under-budget bad patches still miss three positive edge samples. All workers have exited.

Three matched-pair overapproximation seeds use compatible outside-star first-OR gates to cover the six private neighbors of two centers, then add the common line. They preserve every positive edge but remain invalid: five-point20g/14 false-positive maximal cuts, six-point25g/28 cuts, dense-six-point25g/26 cuts. The SAT agent has their frozen JSONs. The finite quadrangle-closure normalizer verified all156 ordered line pairs and can map any first free line-OR to input OR(0,1); it is a helper, not a Lean theorem.

All preservation packets were independently approved by geometry_route: meta3773-construction-algebra-diagnostic-manifest.json (80files267262B); meta3773-construction-algebra-final-delta-manifest.json (23files65033B); meta3773-six-patch-diagnostic-manifest.json (14files55758B); meta3773-six-dense-final-diagnostic-manifest.json (18files45505B). Total135 distinct artifacts433558B, excluding manifest files. All explicitly distinguish invalid near circuits, solver timeouts, constrained finite UNSAT diagnostics, and genuine positive controls. Root owns Git/push/desk.

2026-11-25T14:33:53.079593+00:00 Final computational outcome: L-meta-3773 remains unresolved. Every complete posted-witness candidate failed at least one condition; the best valid complete circuit has64gates. All workers stopped. Reviewed partial Lean controls/verifier/generator and scoped diagnostics are retained; no target lake build, local checker verdict or proof PR is claimed.
