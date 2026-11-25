# L-gct-231 repository scouting

Agent: library_route. Repository-only search on 2026-11-25. No desk, git, PR, or named-file actions.

Target: a complex 3-dimensional submodule of symmetric 4-by-4 matrices t on which permanent(J+t)=24.

## Directly reusable Lean tools

- `lean/PEqualNP/Outside/L_gct_220.lean`, lines 6–26: `sum_perm_succ` and `perm4`, the latter writing Matrix.permanent on Fin 4 as 24 monomials. Their only dependencies are Mathlib and Defs, so their proof text can be copied into the new gap helper namespace. The same helpers occur in L_gct_222.
- `lean/PEqualNP/Gct/Helpers/LS4/PermFour.lean`: equivalent `sum_perm_four` and `eval_perm_four` for the polynomial presentation. The Matrix.permanent version from L_gct_220 is closer to the target.
- Mathlib `LinearMap.finrank_range_of_inj` and `Module.finrank_fin_fun`: define an injective linear map from `Fin 3 → ℂ` to the matrix function type, choose its range, and obtain finrank 3 directly. Checked construction example: `L_gct_197.lean`, lines 242–260 and its final theorem. Recover the three parameters by evaluating three matrix coordinates.
- An explicit matrix family can be verified by rewriting `perm4`, simplifying its 16 coordinate formulas, and using `ring` / `ring_nf` with the appropriate algebraic relation such as `Complex.I_sq`.

## Nearby constructions and their limits

- `L_gct_222`: row/column hook with separate zero-sum constraints. Its symmetric restriction has dimension 2, not 3.
- `Gct/Helpers/LevelLow.lean` and `Gct/L080.lean`: general permanent-level hook of dimension 2n−3. At n=4 this is a nonsymmetric 5-dimensional family; imposing symmetry again leaves dimension 2.
- `L_gct_220`: a checked 1-dimensional circulant direction with first row `[1,I,-I,-1]`; it is not symmetric. `L_gct_221` checks that the alternate Fourier direction `[1,I,-1,-I]` gives permanent 48 at parameter 1 rather than 24.
- `L_gct_197`: checked 5-dimensional family with cube root ω, ω²+ω+1=0:

  `[x,-x,y,-y]`

  `[ωx,-ωx,ω²y,-ω²y]`

  `[ω²x,-ω²x,ωy,-ωy]`

  `[a,b,c,-a-b-c]`.

  An exact search over all 24 relative row/column permutations found that every resulting family intersects the symmetric matrices only at zero. Simultaneous row/column permutations preserve symmetry, so these 24 cover all 576 independently permuted families. Computation was over the exact number field Q(sqrt(-3)), with six symmetry constraints in five parameters; all constraint matrices had rank 5.

  Source and full log: `/tmp/oec/pequalnp-pilot-75/gct231/library/permuted197.py` and `permuted197.log`. This is an exploratory computer result, not a Lean theorem.

- `L_gct_216` is an upper bound 3 for doubly centered 4-by-4 level spaces; it supplies no existence witness. `L_gct_217` bounds row-centered spaces by 5. `L_gct_214` bounds general spaces by 6. These do not establish the requested symmetric existence statement.
- `L_gct_224` is a negative result for 2-dimensional circulant spaces on 6-by-6 matrices, not a 4-by-4 symmetric construction.

## Scout references

No `barriers/l037/STATE.md` or `plan/README.md` exists in this clone. A bounded filename search found only our earlier `results/orch/STATE.md` and unrelated checked L037 modules. No repository theorem with the requested symmetric 3-dimensional conclusion was found.

The missing mathematical step remains an explicit symmetric 3-parameter family (or a proof that none exists); the Lean expansion and dimension bookkeeping are available.

## Independent review of shared helpers

`/tmp/oec/pequalnp-pilot-75/gct231/lean/Helpers.lean`, SHA256 `428d0f7caffd36ebe05e217bf8069fb4527007eeb54643aa3188532743e9e3d0`: PASS. Independently compiled with exit 0 and empty full log `gct231/library/helpers-review-build.log`. The range wrapper retains injectivity, symmetry, and permanent constancy as explicit hypotheses; it does not assert the missing family exists. The symmetric permanent formula is the standard 17-term form. Format checks found no prohibited constructs.

`ThreeMap.lean`: the only addition to Helpers is the expected linear map sending `(x,y,z)` to `xA+yB+zC`, with linearity proved by ring identities. Source-level review passes; compilation was performed by its author.

`Diagonal.lean`, SHA256 `723067e42cc50c0204a39d0d787dc2c821fd4fa7ca84f7cf197556194c60853f`: PASS. Independently compiled with exit 0 and empty complete log `gct231/library/diagonal-review-build.log`. New claims are diagonal_entries_zero and diagonal_rigid: a purely diagonal direction whose entire scalar line has permanent 24 must vanish. The evaluations at ±1 and ±2 correctly recover e₁ through e₄ from `24 + 6e₁z + 2e₂z² + e₃z³ + e₄z⁴`; the monic quartic then forces each entry to have fourth power zero. This does not force the diagonal entries of general, non-diagonal level directions to vanish. The independent mathematical reviewer status_review also confirmed this distinction and argument. Format review passes.

`Projection.lean`, SHA256 `3f018366fc7e3c7b198c2c912c72a598be9a19e75dd50e1fba5a431b2ba3d9f8`: PASS. Independently compiled with exit 0 and empty complete log `gct231/library/projection-review-build.log`. The only additions beyond Diagonal prove that all off-diagonal entries determine a member of any level submodule, define the six upper-triangular coordinates as a linear map, and prove this map injective on a symmetric level submodule. Applying diagonal rigidity to all scalar multiples of the difference is justified by submodule closure. Symmetry recovers the six lower-triangular entries. There is no dimension hypothesis or unconditional existence/nonexistence claim. Format review passes.

`Chart.lean`, SHA256 `2ab78894bc75a12e1b5f5519078f5d0516b0cf71df4d98f17adba8705b104a42`: PASS. Independently compiled with exit 0 and empty complete log `gct231/library/chart-review-build.log`. Byte comparison confirmed the previous Projection prefix and the frozen Selection theorem are unchanged. Six coordinate functionals span the dual because the map into complex six-space is injective. A basis selected from that spanning set has three elements by the stated finrank hypothesis; its coordinate indices are distinct by basis linear independence. Evaluation on that dual basis gives an injective map to complex three-space, hence a bijection by equal dimensions. The final corollary still assumes the candidate submodule, dimension 3, symmetry, and permanent constancy. No existence or refutation claim is added. Format review passes. Axiom auditing is left to the root's integrated-file audit.

## Independent equation-generator review

Requested by finite_cases. The shared generator `gct231/chart_groebner.py`, SHA256 `9db1e1d39cc788b7bbc50169401f5d3f6c1d378e46b6cc85431c241c5d9f9d16`, correctly normalizes the three pivot entries to x,y,z, represents every remaining entry linearly, and eliminates the final diagonal by total-entry sum zero. The latter is the vanishing first derivative of permanent(J+zt), whose linear coefficient is 6 times that sum. Dividing polynomial equations by their nonzero rational contents preserves their complex zero set.

Both supplied star artifacts passed exact independent verification:

- `star-support-buchberger-equations.json`: SHA256 `c822273c0662873783ae82e4b8b12d37a1711dc36ad75d9b538fa1957ade6609`.
- `star-full-generate-equations.json`: SHA256 `805790ef29f0a42c6a57f50e05ef991bd0c2bce219fcd951a4b0965cafcfa1af`.

The verification independently reconstructed the entire permanent polynomial using Ryser inclusion-exclusion, compared all 31 expected coefficient equations in degrees 2–4 exactly, checked matrix symmetry and every normalization constraint, and performed 24 exact integer sample comparisons against the direct 24-permutation definition for each artifact. Complete verifier: `/tmp/oec/pequalnp-pilot-75/gct231/library/verify_chart_equations.py`; full successful log: `chart-equations-review.log`, exit 0.

This review validates the equation generation only. It does not certify the reported support-only Groebner basis, rerun that calculation, establish a full-chart contradiction, or produce a Lean refutation.

## Finite edge-orbit review

`EdgeOrbits.lean`, SHA256 `39b4bc343d440e27c44b802ff35948abcbcee6a52815ea0546e29d5d1251e2fd`: PASS. Independently compiled with exit 0; complete log `gct231/library/edge-orbits-review-build.log` is empty. The proof uses ordinary kernel-checked `decide` and only the permitted limit options.

The endpoint order is 01,02,03,12,13,23. The canonical triples are consequently star 01/02/03, triangle 01/02/12, and path 01/12/23, exactly the three solver charts. The permutation p relabels vertices, q reorders the selected coordinates, and equality up to endpoint flip is appropriate for symmetric matrices. The theorem proves coverage by these representatives, sufficient for chart reduction; it does not separately assert uniqueness of the orbit type.

An additional independent Python enumeration checks all 120 ordered injective coordinate triples and finds a unique orbit type for each: 24 star, 24 triangle, 72 path. Equivalently the 20 unordered triples divide into 4 stars, 4 triangles, and 12 paths. Source `gct231/library/verify_edge_orbits.py`, complete log `edge-orbits-enumeration.log`, exit 0. This auxiliary enumeration is not part of the Lean proof.

## Total-entry condition review

`TotalEntry.lean`, SHA256 `cccbec5cd97f35fef3c3c6dba7044faef40d284fe66738210a4666fe880db7d5`: PASS. Independently compiled with exit 0 and empty complete log `gct231/library/total-entry-review-build.log`. The frozen Helpers prefix is unchanged. For any matrix, without symmetry assumptions, constancy of permanent(J+zt) on its scalar line implies total-entry sum zero. The ±1 and ±2 evaluations use the same odd-coefficient interpolation as diagonal rigidity: the cubic coefficient cancels and the linear coefficient, equal to six times the entry sum, survives with coefficient 1/6. The submodule specialization correctly invokes scalar closure. This supplies the Lean justification for eliminating diagonal33 in the solver charts. Format review passes.

`DiagonalElimination.lean`, SHA256 `38f3337461e392e7974b3dc8b98a97912186ac12aa2e23079a16ddb2bebb92f1`: PASS. Independently compiled with exit 0 and empty complete log `gct231/library/diagonal-elimination-review-build.log`. The previous TotalEntry prefix is byte-preserved. The new corollary uses only symmetry and total-entry sum zero to give t33 as minus the other three diagonal entries minus twice the sum of the six upper entries, exactly matching the solver chart substitution. Format review passes.

## Integrated partial checkpoint review

Named file `lean/PEqualNP/Outside/L_gct_231.lean`, 283 lines / 11845 bytes, SHA256 `e00208d33be08325120dce94fa9632031bb0cfbe1cb3595f8e90982e1b11b8ea`: integration and red-team format review PASS. Exact comparison verifies the Chart prefix, all three new DiagonalElimination declarations with their options, and the EdgeOrbits bodies/options are preserved. Every component was independently compiled during the reviews above; the root is running integrated build04. There is one auxiliary namespace, two permitted imports, no prohibited constructs or text, and only allowed limit options. The source remains partial necessary conditions plus the conditional range construction wrapper; it does not declare the required main theorem. The reported checker rejection `no-theorem` is therefore expected and must not be represented as acceptance.

Review script `gct231/library/review_integration.py`; complete successful log `integration-review04.log`, exit 0.

## Formal coefficient extraction prototype

`/tmp/oec/pequalnp-pilot-75/gct231/library/CoefficientCore.lean`, SHA256 `7e6861ee445e8591a13f5dae87c5f37631b83bd6d1dc5d1cde644b86f1fd8d43`, 34 lines: compiled with exit 0. Full log `coefficient-core-build.log` contains only unused-simp-argument warnings. The original is frozen unchanged; cleanup is confined to later artifacts. Root independently reviewed its scope and source.

The useful route is to identify the literal xy coefficient with `constantCoeff (pderiv 0 (pderiv 1 p))` via Mathlib's `coeff_pderiv`. For four affine three-variable factors, Leibniz's rule leaves just the twelve choices of distinct factors contributing x and y. This avoids expanding irrelevant cubic/quartic monomials or enumerating Finsupp antidiagonals. The file proves that exact twelve-term formula, additivity, and vanishing on constants.

The separate `FullStarCoefficient.lean` is now frozen and compiled PASS: 80 lines / 4754 bytes, SHA256 `4deb2bc9e8e6747c515336f607194f8a07b965e540b40a7274d3e72d1cea2d35`. Full successful log `full-star-coefficient-build3.log` is empty, exit 0. Earlier attempts are retained in the first two build logs; their only failure was the final constant-numeral wrapper, repaired by explicitly instantiating `mixed_nat 24`. The nontrivial coefficient calculation itself elaborated on the first attempt.

This file defines the full normalized star matrix using 18 unrestricted complex parameters d0 through d8 and o0 through o8, proves its literal xy coefficient equals the exact polynomial in the independently reviewed CAS JSON, and proves that coefficient vanishes if the formal permanent equals 24. There is no specialization setting the nonpivot off-diagonal entries to zero. The six z-coefficients naturally do not occur in this particular xy coefficient, but remain unrestricted in the matrix and formal-identity premise. Finite_cases independently reviewed the frozen source: PASS. Its script checked all 16 matrix entries coefficientwise, the order of all 18 parameters, the literal CAS polynomial in both theorem statements, and the mixed-derivative interpretation. Review artifacts are `gct231/review_full_star_coefficient.py` and `gct231/full-star-coefficient-source-review.log`.

The proof uses a copied/adapted generic polynomial-ring version of the checked L_gct_220 permanent expansion, the twelve-term mixed-derivative lemma, and `ring`. Only Mathlib and Defs are used. Format scan passes. The generator is `gct231/library/generate_full_star.py`; all data is read from the explicitly named JSON artifact. The same differentiation-at-zero method can later handle any required coefficient of total degree at most four, with the expected multi-index factorial factor. No all-31-equation build or full-chart contradiction has been attempted here.

The next bounded prototype is also frozen and compiled PASS: `FullStarHigherCoefficients.lean`, 167 lines / 20273 bytes, SHA256 `73002c5f10b0087f85d3bc176b439e2243a8b54a2cca3992de54b78fdfcc9b62`. Complete log `full-star-higher-build2.log` is empty, exit 0. It preserves the checked full-star matrix and xy foundation, then adds exact literal CAS coefficients and formal-identity vanishing consequences for xyz and x²yz. The original first log is retained: its only error was the final arithmetic normalization 1+1=2 in the factorial bridge; `norm_num` closed that residual goal.

The new `quartic_eq_two_coeff` explicitly derives the repeated-variable factorial 2 from `MvPolynomial.coeff_pderiv`. For four affine factors the xyz derivative gives 24 terms, while x²yz gives twice the 12 assignments of the multiset of variable indices [0,0,1,2] to the four factors. The final coefficient proof cancels 2 over the complex numbers. This confirms the route for both distinct and repeated variables through total degree four without generating all 31 equations. The generation script is `gct231/library/generate_higher_star.py`. No additional symmetry, zero-entry, or parameter restrictions are introduced. Frozen independent source review by finite_cases: PASS. Its script confirms the exact JSON coefficients at every occurrence, unchanged matrix/xy foundation, all 24 cubic and 12 quartic factor assignments, and factorial 2. Review artifacts are `gct231/review_full_star_higher.py` and `gct231/full-star-higher-source-review.log`. Format scan passes.

## Normalized-family connection review

Root's `gct231/StarFamilyDriver.lean`, SHA256 `154ed77de431afd200ca417c498090a4d8586f27ca2008b88e9d980add29deaa`, 71 lines / 3233 bytes: independent source review and recompilation PASS. Complete log `gct231/library/star-family-review-build.log` is empty, exit 0. Byte comparison confirms affine3 and fullStarMatrix are unchanged from the frozen coefficient prototype.

The theorem assumes a linear three-parameter family, symmetry, permanent constancy, and the three star pivot identities. The 18 parameters are exactly its basis-vector entries at the first three diagonals and the nonpivot off-diagonal entries, in the same d/o order as the solver. Linearity expands each entry, scalar closure gives total-entry sum zero, and symmetry plus that sum supplies diagonal33. The pivot hypotheses identify the first row and column. Polynomial extensionality over the complex numbers then proves the exact formal permanent identity needed by the coefficient lemmas. No independent injectivity premise, zero nonpivot entries, or other hidden restriction is used.

This is a scratch driver with an Outside import and two helper namespace blocks. Its intended final integration must use the allowed imports and the single helper namespace, as the root already plans. The mathematical proof and exact source are reviewed; this scratch file is not itself presented as a submission-ready proof of the main gap.

## Integrated checkpoint 06 review

Named file, 624 lines / 28689 bytes, SHA256 `ad7a60b2d369921dde6ee77592c01d528e6e22dbcc22fc9b063d37fa6dc03572`: independent integration review PASS. The 506-line prefix at git commit 0730f662 is byte-preserved. The appended driver bodies match the reviewed source after exactly the planned substitutions affine3→starAffine, Coeff.fullStarMatrix→fullStarMatrix, and Coeff.affine3→starAffine. The PathMinorStrata and BlockScalarRigidity bodies are unchanged modulo their removed wrappers and whitespace. All declarations are inside the single existing helper namespace, with only Mathlib and Defs imports, permitted limits, no duplicate declaration names, and no prohibited constructs.

The new scalar lemmas retain their explicit algebraic hypotheses and do not assert that every candidate satisfies those hypotheses. The normalized-family connection remains conditional on the symmetric constant-permanent linear family and its star pivot identities. There is still no main gap theorem. Root is running integrated build06; the driver itself was independently compiled as recorded above.

Comparison script `gct231/library/review_integration06.py`; complete successful log `integration-review06-final.log`, exit 0. The first review log records a harmless scanner false positive: substring matching for the forbidden command `elab` incorrectly matched `relabel`. The corrected scanner uses word boundaries for commands while retaining literal matching for the anywhere-forbidden text.

## Complete 31-equation interface preparation

The complete full-star interface has been generated from the reviewed JSON in its original equation order: 6 quadratics, 10 cubics, and 15 quartics. The manifest records each zero-based JSON index, exponent, positive integer content, multi-index factorial, and derivative-to-primitive cancellation scale. All 18 complex parameters remain unrestricted. The generator `gct231/library/generate_star31.py` first produced `FullStar31.lean`, 761 lines / 65775 bytes, SHA256 `1d9ce39dfdf8a03b0c818087bd6d243bf209f89840193cf015b9f47cdb55965a`. Its single conjunction proof exceeded a sampled 7 GiB RSS guard without a Lean verdict.

At the root's direction, `split_star31.py` generated one coefficient helper per equation, followed by an exact conjunction wrapper: `FullStar31Split.lean`, 976 lines / 105650 bytes, SHA256 `8f186589489eb33e2a6e9385b336b60e0f5d55513b281eaa978a6288a969602c`. Umbrella-import retries, including a serial profiling retry, also hit the RSS guard quickly. All complete logs and run-status JSON files are retained.

The final candidate `FullStar31Lean.lean` narrows imports to eight Mathlib modules, uses no project imports, and adds a scoped 4-million-heartbeat limit to the final wrapper. Frozen SHA256 `4e3efa0b397320b678920ea30e5c1228261ee1d043e99e6134e2d8be60a9e6a3`, 983 lines / 105951 bytes. Narrow-import build01 used about 4.14 million KiB peak RSS and finished in 97.1 seconds: all derivative helpers and all 31 individual equation proofs elaborated, but the final exact-conjunction theorem exhausted its default 200k heartbeat budget. Build02, with the scoped wrapper limit, is currently running under the root-approved 300-second / 7168-MiB sampled-RSS limits. It is not yet reported as a fully compiled file here.

Independent global_normal_form review: PASS for the original mapping and the final candidate delta. It checked all 16 matrix entries, the exact 24 permutation monomials, complete exponent coverage and JSON ordering, primitive contents, derivative multiplicities, generic factor assignments, factorials, and cancellation scales. The final proof-layout review confirms all 31 individual helpers match the original proof branches, the conjunction statement is unchanged, and the wrapper applies exactly those 31 helpers with the same parameters and hypothesis. Review artifacts are `gct231/fullstar31_review/` and `gct231/fullstar31_delta_review/`; the latter review manifest SHA256 is `ec70e2c40e562b9de491fc595fd3eca5467a35f62b2482aba7ff45001fc3f011`. The final coefficient mapping manifest is `gct231/library/full-star31-lean-manifest.json`.

Final checked milestone: `FullStar31Individual.lean`, 916 lines / 73248 bytes, SHA256 `d7bf606daad095450d7e07956c199a4c53a96aab17ad1d3f93196c405f3fe351`, compiled PASS with all 31 individual primitive-equation lemmas. The larger conjunction-wrapper candidate reached the 300-second cap, so the root directed preserving the useful individual lemmas without that wrapper. The compiled file is a byte-exact prefix of the reviewed candidate, with the final wrapper/option removed and the namespace closed. Independent prefix review PASS is preserved in `gct231/fullstar31_individual_review/`.

Successful complete build artifacts: `gct231/library/full-star31-individual-build01.log`, `.run.json`, and `-wrapper.log`. Compiler exit 0 in 84.875 seconds, sampled peak process-group RSS 4051760 KiB, under 300 seconds / 7168 MiB limits. The log contains profiler output and only deprecation/style warnings: the old Complex.Basic module alias and `<;>` where `;` suffices. No errors. There are only eight Mathlib imports, no project or Outside dependency. Exact final source/import/equation-to-lemma mapping: `gct231/library/full-star31-individual-manifest.json`.

The result covers the complete original 31-equation system, in the original CAS order, as independent lemmas certEq400 through the remaining exponent-labelled cases. It does not prove the system inconsistent, provide a full-chart unit certificate, or prove/refute the main gap. The root was notified immediately on PASS for checkpointing before further work.

Axiom audit of all 31 individual full-star equations: PASS. The fresh scratch
`FullStar31AxiomAudit.lean` contains the frozen checked file unchanged followed by
31 `#print axioms` commands. Its source SHA256 is
`0f21d915a4a3fc9be9b121203e81d487359e729fd2292918467eafce66f50029`.
Compilation exited 0 in 91.47 seconds with peak sampled process-group RSS
4,063,820 KiB. An exact manifest-order check found every certEq theorem and
confirmed its axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`.
Full logs/status/verification: scratch `gct231/library/full-star31-axiom-audit01.log`,
`.run.json`, and `-verified.json`. The frozen original is unchanged.

Reusable block determinant result: scratch `library/BlockDeterminant.lean`
(29 lines, 1260 bytes; SHA256
`e34270ccb9d6610c59a3737b6b906eaf35ea80a6fecd6fe13ef8d3478b9b317f`)
compiles with exit 0. Over every commutative ring it proves
`det(fromBlocks 0 B Bᵀ D) = det(B)^2` for two-by-two blocks and the
change-of-basis form `det(P)^2 * det(M) = det(B)^2` from the stated congruence.
Neither symmetry of D nor invertibility of P is assumed. The existence of an
isotropic plane and an adapted invertible basis is not asserted. Structural
independently reviewed the frozen source and final factor-order delta: PASS.
Build03 exited 0 in 3.05 seconds, sampled peak RSS 3,061,480 KiB. A separate
`BlockDeterminantAudit.lean` confirms both statements use only the three standard
axioms. Full build/audit logs and a manifest remain beside the scratch source.

Geometric bridge milestones, all compiled and frozen:
- `library/PolynomialSquareBridge.lean`, 53 lines: constant invertible polynomial
  congruence with a zero/transpose block gives an explicit determinant square.
- `library/AdaptedPencilSquare.lean`, 95 lines: symmetry and two adapted zero
  blocks imply `det(C(N)-X*C(M)) = p^2`. Build04 and separate axiom audit pass.
- `library/IsotropicColumns.lean`, 145 lines, SHA256
  `62ec7fe825ee51ba7c2ab794433edce721b75d12d4c2f3e178d32dc53ee514b9`:
  pointwise quadratic vanishing polarizes, and an explicit invertible matrix
  whose first two columns belong to the common vanishing submodule satisfies
  the adapted-block hypotheses. Build01 exited 0 in 3.57 seconds; audit01
  exited 0 in 3.55 seconds and confirms only the standard three axioms.
These conditional milestones do not assert the adapted basis exists. That
construction is being proved independently by `fresh_main_proof/c3_review`.
All complete logs and scope manifests are beside the corresponding scratch files.

Complete common-isotropic-plane bridge: PASS. The 200-line standalone scratch
`library/CommonIsotropicPlane.lean` (9039 bytes; SHA256
`ddd00bd47c8437801018a3ecb47e1929f2527ad63efdfd88ee328ed611838756`)
proves the determinant pencil of two symmetric complex four-by-four matrices
is a polynomial square whenever both quadratic forms vanish on a common
submodule of finrank two. Unlike earlier milestones, this theorem constructs
the adapted invertible matrix rather than assuming it.

The adapted basis was independently implemented and compiled by
`fresh_main_proof/c3_review`: `adapted-basis/AdaptedBasis.lean`, SHA256
`490d6f557ea62c82aa6eebb0843e32c34c60af26d0c752661654b14df0159f3c`.
My exact-source review passed: a complement has finrank two by dimension
additivity; the product of two finite bases maps to an ambient basis; its
first two vectors lie in the specified submodule; column independence gives
a nonzero determinant. No isotropy, nonsingularity, or adapted-basis existence
is silently assumed. Its proof bodies were copied unchanged into the aggregate
auxiliary namespace. The prior 145-line geometric proof bodies are unchanged
too; only imports were combined and the deprecated Complex import replaced.
The final nine-line theorem obtains this matrix and invokes the checked
polarization/column-membership criterion.

Aggregate build01 and audit01 each exited 0 in 4.06 seconds. The final theorem
and adapted matrix existence use only `propext`, `Classical.choice`, and
`Quot.sound`. Full logs/status and `common-isotropic-plane-manifest.json` are
beside the scratch source. This proves the requested reusable geometric
criterion, not the full posted L-gct-231 existence statement.

The complete 200-line bridge also passed independent body-preservation and
final-statement review by both structural and the adapted-basis author.

A small companion `library/PolynomialNonsquare.lean` (24 lines, 971 bytes;
SHA256 `a00e214f4f3390128431db17af70a7211ac730b705d3e92bc193563f8cd95451`)
proves over a commutative ring without zero divisors that a polynomial with
coefficients zero at degrees zero and two, and nonzero at degree three, cannot
be a square. No degree bound is assumed. The proof first forces a hypothetical
square root's constant and linear coefficients to vanish, then contradicts
the cubic coefficient. Build03 and separate audit01 exit 0 with only the
standard three axioms. This criterion matches the separately derived C4
determinant `λ³(13λ−4)/4`; the explicit determinant computation is a separate
obligation and is not silently included here.

Quartic-square coefficient bridge: PASS. Frozen scratch
`library/QuarticSquareCoefficients.lean` (43 lines, 1804 bytes; SHA256
`24051b7d2e1729780f4d74b6532e792dcca4bbda93fb443a9f6629f6b4f24a35`)
proves both `8 a^2 d - 4 a b c + b^3 = 0` and
`(4 a c - b^2)^2 - 64 a^3 e = 0` from `q=p^2` and
`natDegree q <= 4`, where a,b,c,d,e are q's coefficients at 4,3,2,1,0.
The proof is valid over any commutative ring without zero divisors, including
complex numbers. It uses no nonzero leading coefficient, exact-degree, or
characteristic-zero assumption and performs no division. Degree multiplicativity
bounds the square root's degree by two; five explicit convolution formulas
reduce the identities to ring normalization. Independent review by c3_review
passes. Build01 and separate audit01 exit 0; only standard axioms occur. Full
logs/status and a scope manifest are beside the source.

Direct geometric-to-scalar composition: PASS. Frozen standalone scratch
`library/CommonPlaneCoefficientIdentities.lean` (266 lines, 12024 bytes; SHA256
`1aaaa15f2afadc317c741261a7fb57dad2dc2f408c8c41726940c7568919e522`)
preserves the earlier common-plane and quartic coefficient proof bodies exactly.
It then uses Mathlib's `Polynomial.natDegree_det_X_add_C_le` with A=-M, B=N
to bound the four-by-four pencil determinant's degree by four, and concludes
both scalar square conditions from the shared two-dimensional isotropic
subspace alone. No nonzero determinant, exact quartic degree, explicit adapted
basis, explicit square witness, or degree hypothesis remains in this final
corollary. Degenerate pencils are included.

Build02 exited 0 in 7.13 seconds; separate audit01 exits 0 and verifies only the
standard three axioms. c3_review independently checked exact body preservation,
the pencil sign convention, cardinality-four bound, and final assumptions:
PASS. Complete logs/status and the final `common-plane-coefficients-manifest.json`
are beside the frozen source.
