# Lean formalization route for L-gct-231

The exact target asks for a three-dimensional complex submodule of symmetric 4 by 4 matrices on which the permanent of the all-ones matrix plus the submodule element is constantly 24.

Compiled helper source: `/tmp/oec/pequalnp-pilot-75/gct231/lean/Helpers.lean`; full successful compile output: `helpers-build5.log` (empty, exit 0). Imports are exactly Mathlib and PEqualNP.Defs. No concrete three-dimensional witness or main theorem is asserted yet.

- `range_witness` obtains the exact existential target from an injective complex linear map out of `Fin 3 → ℂ`, together with symmetry and permanent identities for its image. It uses `LinearMap.finrank_range_of_inj` and the standard finrank of functions on `Fin 3`.
- `injective_of_coordinates` reduces injectivity to recovering the three input coordinates from three matrix entries.
- `sum_perm_succ` and `perm4` are exact declaration-body copies from `lean/PEqualNP/Outside/L_gct_220.lean` in the new gap-owned helper namespace. They expand the permanent into its 24 permutation monomials using ordinary Lean proofs.
- `symmetric_permanent` collects the expansion into the 17 usual monomials in ten symmetric entries; simplification and `ring` prove it.

For a concrete matrix family, define a linear map from three coefficients, recover three coordinates (or otherwise prove injectivity), and prove the permanent identity with `perm4`, simplification of matrix entries, `ring_nf`, and `Complex.I_sq` if needed. The helper contains no sorry, new axiom, native_decide, forbidden root identifier, string literal, or non-simp attribute.

The direct simplifier expansion initially looped between permutation-universe lemmas; this was replaced by the existing short checked expansion. Only the successful source and complete compile output should be checkpointed as proof evidence. Earlier failed-build logs are diagnostics in scratch.

Independent source review and separate recompilation PASS by library_route. Their full successful log is `/tmp/oec/pequalnp-pilot-75/gct231/library/helpers-review-build.log` (empty, exit 0).

Helper SHA256: `428d0f7caffd36ebe05e217bf8069fb4527007eeb54643aa3188532743e9e3d0`; 66 lines, 3019 bytes.

## Diagonal rigidity and projection

`Diagonal.lean` in the same scratch directory compiles successfully with an empty complete `diagonal-build.log`. Its SHA256 is `723067e42cc50c0204a39d0d787dc2c821fd4fa7ca84f7cf197556194c60853f` (106 lines, 4,866 bytes). library_route independently reviewed and recompiled it successfully; the complete independent log is `gct231/library/diagonal-review-build.log`.

`diagonal_entries_zero` proves that a diagonal perturbation with constant permanent along every complex scalar multiple is zero. Evaluating at 1, -1, 2, -2 extracts all four elementary symmetric coefficients by explicit linear combinations. The identity obtained by evaluating the characteristic polynomial at each diagonal entry yields its fourth power equal to zero. `diagonal_rigid` packages this for a function on `Fin 4`.

This is a necessary condition, not a refutation of the posted three-dimensional statement. The separate `Projection.lean` extension compiles successfully (159 lines, 6,719 bytes; SHA256 `3f018366fc7e3c7b198c2c912c72a598be9a19e75dd50e1fba5a431b2ba3d9f8`; complete empty `projection-build2.log`). Within a constant-permanent submodule all off-diagonal entries determine the diagonal. For a symmetric submodule the explicit linear map to positions 01, 02, 03, 12, 13, 23 is injective. No finrank assumption is needed. Independent source/scope/format review and separate recompilation PASS by library_route; complete independent output is `gct231/library/projection-review-build.log` (empty, exit 0).

## Three-coordinate chart selection

The standalone `Selection.lean` compiles with exactly Mathlib and PEqualNP.Defs (59 lines, 2,309 bytes; SHA256 `b3280b52d42a81a570d943197fc45f281068867083264605b64909b05a4dad22`). Full `selection-build2.log` is empty, exit 0.

`select_three_coordinates` states that if a finite-dimensional complex vector space V has finrank 3 and F : V →ₗ[ℂ] (Fin 6 → ℂ) is injective, there is an injective choice of three of the six coordinates for which the restricted map V → (Fin 3 → ℂ) is bijective. The coordinate functionals separate points and hence span the dual. A basis selected from this spanning family has three elements; evaluating at this dual basis gives an injective map, and equal dimensions give surjectivity. No matrix minor calculation is needed.

Independent source/scope/format review and separate recompilation of the combined selection/chart result PASS by library_route; the complete independent log is `gct231/library/chart-review-build.log` (empty, exit 0). The combined `Chart.lean` includes the reviewed projection helpers, the new selection lemma, and its direct application to a symmetric three-dimensional constant-permanent submodule. It compiles successfully (225 lines, 9,465 bytes; SHA256 `2ab78894bc75a12e1b5f5519078f5d0516b0cf71df4d98f17adba8705b104a42`; complete empty `chart-build.log`, exit 0). No S4 orbit classification or polynomial-system certificate is included.
