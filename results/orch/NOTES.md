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
