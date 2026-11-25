# L-gct-231 orchestration notes

Root holds only its assigned L-gct-231 lease, acquired 2026-11-25 09:35:53 UTC.
Exact statement: there exists a complex-linear dimension-three subspace of symmetric 4x4 matrices T with permanent(J+T)=24 for every T, J all ones.

Assignments:
- construct_search: explicit symbolic construction.
- geometry_search: homogeneous coefficient constraints, geometric route or obstruction.
- status_review: Lean range/injectivity/finrank bridge, own Dimension.lean.
- toolchain_setup: Lean Fin4 permanent expansion, own Permanent.lean.
- artifact_analysis: locate scout context or public primary sources.
- root: integration, lease, independent review coordination, push and PR.

Append findings under your own heading. Only root edits final lean/PEqualNP/Outside/L_gct_231.lean.
Scratch lemmas are coordination artifacts, not the final PR diff. Helpers in the final file must be inside its module-named namespace, final fully qualified theorem last.

Environment: source /tmp/oec/pequalnp-pilot-78/toolchain/env.sh. Keep holder PID 4303 alive. Selective builds work; full checker smoke currently resource-blocked by 8 GiB memory/7.9 GiB disk. Never build Mathlib from source. Full build/check output must be retained.


## Construction search: star-plane extension obstruction

At 2026-11-25 09:40 UTC, exact SymPy coefficient elimination shows the standard 2D star flat cannot extend to a 3D flat. Write its nonzero entries T01=T10=a, T02=T20=b, T03=T30=−a−b. For arbitrary symmetric V, requiring per(J+T+zV)=24 forces from z-linear coefficients the lower 3×3 block of V to equal rJ and V00=−2s−9r, where s=V01+V02+V03. The remaining coefficients are 2(s²−6sr−63r²), 4r(s²−6sr−39r²), and 2r²(s−9r)(s+3r). The first two give 96r³=0, hence r=0 and s=0, so V is already in the star plane. This is an exact symbolic obstruction to this extension route, not a global refutation. Full computational output is /tmp/oec/pequalnp-pilot-78/construct_search/star-extension.txt.

2026-11-25T09:39:11.459864+00:00 toolchain_setup: COMPILED generic 24-term permanent_four expansion in results/orch/lemmas/Permanent.lean. Uses permitted Mathlib-only imports, computable permsOfList enumeration, simp+ring; no sorry/native_decide. Parent notified for immediate review/push. Exact Lean/Mathlib pins unchanged.


## Linear-algebra and star-plane formalization

2026-11-25T09:41:34.269629+00:00 status_review: Dimension.lean compiled: generic injective Fin3 linear-map range has finrank3, coordinate recovery proves injectivity, and range_level_space reduces the target to a parameterized symmetric permanent identity. Star.lean also compiled: starMatrix(a,b) with T01=a,T02=b,T03=-a-b and symmetric entries has permanent(J+T)=24 over any commutative ring. Its complex-linear parameter map is injective and its image has finrank2. The star_two_dimensional lemma is a checked 2D partial lower bound, not the 3D target. Parent notified for push-early. Full logs are dimension-build-2.txt and star-build.txt in scratch.

2026-11-25T09:41:48.614427+00:00 toolchain_setup: permanent_star also COMPILED in Permanent.lean. For the all-ones matrix plus symmetric star entries a,b,c and center d, permanent = 24 + 6*d + 12*(a+b+c) + 2*(a+b+c)^2. In particular c=-a-b,d=0 gives the established two-dimensional constant-permanent star flat. Four selective Mathlib imports; empty compiler output.

## Construction search: small exact directions and nonstar planes

Exhaustive Gaussian alphabet {0,±1,±i}, modulo unit scaling and with total entry sum0:37,177 candidates,30 directions satisfying all four polynomial coefficients;12 compatiblepairs and4 triangles, everytriangle dependent. Real alphabet−2..2, first nonzero positive:255,186 candidates,132 valid directions,408 compatiblepairs,764 triangles, everytriangle dependent. After primitive dedup,120 directions generate24 distinct compatible2D planes, all hollow. S4-permutation orbits have sizes4(star),12,8.

Arbitrary symmetric extensions of the two nonstar representatives also fail. Quotienting by the oldplane, the size12 representative leaves parametersu,r and exactly the same three equations as the star obstruction. The size8 representative leaves V=r[[1,0,0,−5],[0,1,1,−4],[0,1,1,6],[−5,−4,6,1]], and coefficientz²=−16r². Thus all24 found hollowplanes are maximal2D flats. This is not a classification of allcomplexhollowplanes, nor a globalno3Dproof. Exact scripts and logs live in scratch/construct_search/{search.cpp,extend_planes.py,real-planes.txt,plane-orbits.txt,extend-planes.stdout}.


## Exhaustive finite-field geometry

2026-11-25T09:47:31.857222+00:00 status_review: Exhaustively enumerated projective symmetric tangent directions over F5 and F7, imposing all four homogeneous coefficients of permanent(J+zT)-24. F5: 488281 directions, 3918 good, 2340 pairwise-compatible edges, 3120 triangles, zero independent compatible triples, hence zero 3D flats. F7: 6725601 directions, 17088 good, 6608 edges, 13220 triangles, four independent compatible triples, all rejected by full mixed degree≤4 identity, hence zero 3D flats. Every independent F7 triple has diagonal-map rank3. Counts of 2D flats by diagonal-map rank0/1/2: F5=24/72/60; F7=24/56/156. These are finite-field results only, NOT a refutation over complex numbers. Independent Python polynomial-convolution spot checks passed for sampled directions and spans. Source and full stdout/stderr are in scratch finitefield/. Search source SHA256 03eba20869b854c2d1a351e2ddcf01bca3df3d876d1cda15e7fe6fb9bc2d59c4.


## Geometry search: restricted-family obstructions

2026-11-25T09:49:22.345256+00:00 geometry_search / child rowzero: exact symbolic calculations give several obstructions, not a global Lean refutation.

- Row-sum-zero matrices have Hadamard form T=HSHᵀ for symmetric3×3 S. Homogeneous terms are16 tr(S²) and64 per(S). Maximal-isotropic3-plane skew-chart equations yield Gröbner basis[1]; other charts are sign-conjugate. Scripts: geometry_search/rowzero/chart.*.
- A flat from two independent diagonal2×2 blocks with slopes−1±√2 cannot extend to3D. All projective third-direction charts yield Gröbner basis[1]. Scripts: geometry_search/rowzero/extend_blocks.*.
- For fixed isotropic kernel u=(1,−1,i,−i), impose Tu=0 andsumT=0. This5D space has quadratic rank2. Put w=(1,1,−1,−1),j=ones. Each quadratic-isotropic4D component is T=a uuᵀ+b(uwᵀ+wuᵀ)+c(ujᵀ+juᵀ)+e(±√6 wwᵀ+wjᵀ+jwᵀ). Its cubic/32 is ±√6 a²e+2ab²−2b²e∓4√6 bce+6c²e±2√6 e³. This has no linear factor: restriction e=0 forces any factor to be a+ke or b+ke; substitution leaves respectively6c²e or±√6a²e. Thus this slice contains no3D flat.
- For u=(1,ω,ω²,0), analogous cubic/6 equals a³+8(c−2b)(c+b)²+(320±224√2)e³, also no linear factor. Child is completing the generic isotropic-kernel parameter analysis.
- Radical2D spaces T=v hᵀ+h vᵀ with sumv=v²=1 andh⊥1,v are flats only for coordinatevectors v=e_i (the known stars). In chart v=(a,b,c,1−a−b−c), c≠d, impose the norm, cubic/quartic coefficients and z(c−d)=1. Exact Gröbner basis is {a,b,c²−c,z−2c+1}; permutations cover every admissiblev. Scripts: geometry_search/rowzero/radical_flats.*.
- Consequently fixed-kernel slices with (sumu)²=3u² cannot contain3D flats: their quadratic rank3 forces a maximal isotropic3-plane to contain the2D radical, which would be a star and cannot extend.
- Fixed-kernel slices with (sumu)²=4u² andu²≠0 have quadratic rank4 with a1D radical spanned w wᵀ, where sumw=w²=0. This rankone line cannot be a flat: its degree3 and4 terms forcee3(w)=e4(w)=0, so all four coordinates ofw vanish.

Remaining gap: no argument presently shows that an arbitrary3D constant-permanent space has a common kernel.


### Geometry update: generic isotropic kernels and Plücker test

2026-11-25T09:55:22.461433+00:00

Child rowzero completed the generic isotropic-kernel radical cubic obstruction. In the conic parametrization u(t)=(1−t²)h1+i(1+t²)h2+2t h3, with Hadamard columns hi and w=u'/2, write q=t⁴,F=q−1. The cubic on T=a uuᵀ+b(uwᵀ+wuᵀ)+c(ujᵀ+juᵀ) is A a³+B a²b+C ab²+D b³+E b²c−E c³, where A=−1536t²F², B=−1536tF(5q−1), C=−256(49q²−34q+1), D=−512t³(13q−5), E=768itF. When tF≠0, any linear factor forces H(q)=q³−33q²−33q+1=0 and K(q)³+54q(q−1)^4=0, K=q²+14q+1. But K³−H²=108q(q−1)^4, giving a contradiction. Exceptional kernels are permutations/scalings of(1,−1,i,−i), handled above. Thus every isotropic fixed-kernel slice with sumu=0 excludes3D flats. Exact scripts/logs: geometry_search/rowzero/isotropic_radical.*.

A speculative six-linearly-embedded-quadric decomposition of the plane space was not supported. F5 has156 planes, F7 has236 rather than384. Sampling10,000 vector4-spans of the F5 Plücker points found9,993 spans containing4points,6containing5points,1containing6points, none≥8. This is exploratorysampling, not a proof. Script/output: geometry_search/plucker_cluster.py andplucker-cluster.stdout.

Construct_search reports generic nonstar2flats have invertible matrices and no common kernel, so a common-kernel reduction for arbitrary3flats remains unproved and cannot be assumed.


## Hollow-flat dimension obstruction

2026-11-25T09:57:03.971724+00:00 artifact_analysis: COMPILED results/orch/lemmas/Hollow.lean (168 lines), including hollow_flat_finrank_le_two. Every complex-linear subspace of symmetric zero-diagonal 4x4 T with permanent(J+T)=24 has finrank at most2. Scalar closure and the explicit permanent polynomial give edge sum S=0 and opposite-edge quadratic R=af+be+cd=0. Polarizing R gives the nondegenerate opposite-edge bilinear form on six coordinates. The all-ones vector belongs to W-orthogonal by S=0 and lies outside W because R(ones)=3, so W is strictly smaller than its orthogonal complement; finrank then is at most2. Edge coordinates inject on symmetric hollow matrices. This excludes dimension3 only under the zero-diagonal hypothesis; it is not a global refutation. Build exit0 and empty diagnostics in scratch/hollow-build-4.stdout and scratch/hollow-build-4.stderr. Root notified for push-early preservation.

2026-11-25T09:57:21.416005+00:00 status_review: F11 exhaustive completed in 327.17s: 235794769 projective tangent directions, 172128 good, 17424 compatible edges, 58080 triangles all collinear, zero 3D flats. There are 264 2D flats, diagonal rank 0/1/2 counts 24/0/240. Independent Python coefficient spotchecks passed. F13 compiled parallel variant awaits root renewal. All finite-field evidence remains insufficient to refute complex target.

2026-11-25T09:58:58.771691+00:00 status_review: Independent review of artifact_analysis Hollow.lean PASS: checked coefficient extraction, isotropy and strict orthogonal inclusion, edge-map injectivity, namespace/plain-file constraints. Independent lake env lean rebuild exited 0 with empty stdout/stderr, retained in hollow-independent-review.stdout/.stderr. Scratch self-module import must be removed during integration. F13 exhaustive search launched after root renewal at09:57:29; sparse four-thread implementation uses low memory.


### Geometry completion: hollow planes and duplicated-row slice

2026-11-25T10:00:23.790636+00:00

ALL complex hollow2D flats have now been classified exactly: four admissible OGr(2,5) charts give17roots in each even chart and18roots in each odd chart; their RREF union is exactly24 rationalplanes. Direct expansion verifies all24, and S4 orbits have sizes4,12,8. Exactbases and chartwitnesses: geometry_search/rowzero/hollow_planes.json. Coverage is elementary: if all four admissible projections fail, either a coordinatepair spans2 and isotropy equates a rank2 quadratic with a square, or all coordinatefunctions (includingZ) arecollinear; both contradictdimension2. Combined with construct_search’s nonextension calculation for the3orbits, any3Dflat must have diagonalprojectionrank at least2.

The entire duplicate-row fixed-kernel slice u=e1−e2 has NO2D flat. This closes the proposed route adjoining the basicstar direction A01=1,A02=−1. Reorder the repeated pair first and write M=[[a,a,b,c],[a,a,b,c],[b,b,d,e],[c,c,e,f]]. Its permanent is2a²(df+e²)+8abce+4a(b²f+c²d)+4b²c².

If a varies, normalizea=1+z. On the affine linez=−1, constantpermanent forcesb²c²=6, henceb,c are units inC[h] and depend onlyonz: b=1+Bz,c=1+Cz. The second direction is supported in(d,e,f), and normalizing its middleentry to1 gives slopesP=−1±√2,Q=1,R=−1∓√2. The remaining tangent identity determinesF and mixedcoefficients determineD; one then obtains
(B−C)*[(1+√2)B+(√2−1)C−2√2]=0.
The branchB=C has z² coefficient−8(B²+6B+3) and z³ coefficient−16B(B+1)², with no commonroot. The otherbranch C=4+2√2−(3+2√2)B also has coprime quadratic/cubic coefficients. The exact expressions are in geometry_search/duplicate-shortcut.stdout. Independent childreview supplied elementary contradictions, so no Gröbner proof is needed for this step.

If a is constant1, write b=1+β,c=1+γ,d=1+δ,e=1+ε,f=1+φ. The quartic4β²γ² forcesoneofβ,γ to vanish; assumeβ=0. Ifγ≠0, cubic4γ²δ forcesδ=0 and per=6f+2(e+2c)² then forcesφ=0,ε=−2γ, givingdimension≤1. Ifγ=0 too, tangentφ=−δ−2ε and quadratic−δ²−2δε+ε² factor into two linearforms, again givingdimension≤1. Entirecoverage and normalization were independently reviewed byrowzero.

These are mathematical/symbolic obstructions, NOT a Lean proof of the postednegation. A general3D space with no commonkernel and diagonalprojectionrank2or3 is still not excluded.

### Toolchain/numeric update 2026-11-25 10:05 UTC

Global complex least-squares search: 5,480 starts across all 120 coordinate charts and 1,250 random tangent gauges found no zero (best scaled residual about 0.0018174). This is numerical evidence only. Full scripts/logs are in `/tmp/oec/pequalnp-pilot-78/numeric/`.

Native msolve 0.11.0 now runs from `numeric/cas/bin/msolve`, installed from published-SHA256-verified Julia BinaryBuilder/Yggdrasil GitHub artifacts. Upstream msolve source pin is cc044551f8e202d00691990fd3fd0b1226a88ea2. FLINT 3.6.1 debugging sections were stripped; every allocated ELF section was hash-verified unchanged. All installed dependencies remain in scratch; no Lean/cache runtime bytes changed. The first characteristic-101 full chart (diagonal coordinate pivots 0,4,7) reached degree 6 with a 39770-by-115456 matrix but was stopped for concurrent Lean-build memory safety; no algebraic conclusion. Heavy CAS is paused pending root clearance. Eleven S4 chart representatives and Q/F101/F2147483647 inputs are generated.

Restored authentic optional `.c` and `.ilean` artifacts for the complete BilinearForm.Orthogonal import closure: 22 files in 11 modules, 1,838,693 bytes. Existing runtime files were compared against the official pinned archives and untouched. Full restoration log and manifest: `toolchain/orthogonal-restore.*`, `toolchain/orthogonal-restored.json`. Cache executable was re-removed after backup-hash verification.

## Lean-checked star-plane maximality

At10:06UTC, results/orch/lemmas/StarMaximal.lean passed lake env lean with exit0 and empty stdout/stderr. It proves starLinear_zero by four z-evaluations and star_two_plane_maximal: any symmetricV whose addition to every standard2Dstar matrix preserves permanent24 is already in the starplane. Six evaluations of the first-z coefficient force its lower3×3blockconstant; quadratic/cubic coefficients then force that constant and the firstrow sum to vanish. The scratch file imports the compiled partial target and contains a renamed duplicate of quartic_first_coefficients; root can remove this duplicate when merging. Full logs under scratch/construct_search/star-maximal-build.stdout and .stderr.

Independent chart-generator audit (artifact_analysis): PASS. All 11 S4 pivot orbits are disjoint and cover all 120 minors (sizes 12,6,24,24,12,4,6,12,4,4,12). Exact Fraction checks compared 1,705 evaluated polynomial coefficients across 55 chart assignments and 110 direct permanent evaluations; all matched. Modular infeasibility alone does not imply infeasibility over Q/C. A rigorous global refutation still requires characteristic-zero certificates for every chart and their Lean verification.

2026-11-25T10:07:19.099715+00:00 status_review: Independent review and rebuild of construct_search StarMaximal.lean PASS. All 126 lines reviewed, no forbidden plain-file constructs, only allowed scoped heartbeat limits. Six interpolated linear constraints force the lower block to rJ and V00=−2s−9r; scalar coefficients then give 96r³=0 and s²=0, hence V is in the original star plane. Independent compiler exited 0 with empty star-maximal-independent.stdout/.stderr. Scratch self-import and duplicated coefficient helper should be removed at integration.


## Geometry test: rank-three singular directions exist

2026-11-25T10:07:45.708286+00:00 The proposed auxiliary claim that every singular symmetric constant-permanent direction has rank≤2 is FALSE, even overR. Set b=(3+√7)/2,c=(3−√7)/2 and
T=[[-8,b,c,0],[b,1,0,0],[c,0,1,0],[0,0,0,0]].
Then b+c=3,b²+c²=8,bc=1/2. Direct exact24-term expansion gives per(J+zT)=24 identically. The upper-left3×3 determinant is−16 and the lastrow iszero, so rankT=3. This refutes ONLY the auxiliary structural lead, NOT L-gct-231.

The132smallreal directions in construct_search/directions-real.txt have ranks36ofrank2 and96ofrank4, explaining why that sample missedrank3. Finitefield valid-direction datasets containmanyrank3 directions: F5=828,F7=2240,F11=15984. Rank3 directions also occurinsideenumerated2flats, with incidencecounts228,380,408 respectively. Thosefinitefieldstatistics are not bythemselves characteristic-zero statements.
