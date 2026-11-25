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
