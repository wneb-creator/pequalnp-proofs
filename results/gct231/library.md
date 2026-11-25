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
