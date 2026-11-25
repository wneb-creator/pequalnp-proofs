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
