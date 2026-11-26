This packet provides the checked symmetry reduction for monotone Petersen edge residuals. Its exported theorem is `PEqualNP.Outside.L_meta_2373.Residual.Orbit.fourteen_targets`.

For `H : Fin 1024 → Bool`, assume monotonicity under bit inclusion, `Fminus ≤ H ≤ F`, and `H 3 = false`. Here `F` is the fifteen-edge Petersen function in the source, `Fminus` removes edge `0–1`, and row `3` sets exactly inputs `0` and `1` to true. The theorem gives:

```lean
∃ k : Fin 14, ∃ g : Fin 8,
  H = fun r => target (reps k) (permRow g r)
```

The representatives, in index order, are `[0, 8, 40, 44, 160, 168, 170, 174, 424, 426, 430, 442, 446, 510]`. The nine exceptional rows, in mask-bit order, are `[3, 11, 131, 139, 259, 387, 515, 523, 771]`. `mask_cover` supplies a checked witness for every one of the 47 listed masks. The exported results prove coverage; they do not prove that fourteen is a minimal orbit count, that the eight permutations exhaust the stabilizer, or that every listed mask is an admissible distinct function.

The direction is a pullback: bit `i` of `permRow g r` is bit `vertices g i` of `r`. The mask witness states `bits m i = bits (reps k) (actions g i)`, and `target_transport` concludes `target m r = target (reps k) (permRow g r)`. `actions g` sends the index of an exceptional row to the index of its permuted row. Inverse indices are `[0, 1, 2, 3, 4, 6, 5, 7]`; indices 5 and 6 are mutual inverses.

Choose one integration mode:

- `ResidualOrbitsStandalone.lean` imports only `PEqualNP.Defs` and contains the classification plus symmetry proof. Use it in a module environment that does not also import the main gap file or the delta.
- `ResidualOrbitDelta.lean` imports `PEqualNP.Outside.L_meta_2373` and adds the symmetry proof to the classification already in that file. Its pinned main revision is `cc06910dad6d57c83b639802d4c71034de91063f`, file `lean/PEqualNP/Outside/L_meta_2373.lean`, SHA256 `87b729f3c29a71fc24aab1fd9427b0422900ac16601d29a7cceacef2cd268ab6`.

The two modes declare the same fully qualified `Residual`/`Residual.Orbit` constants. Importing both, or importing the standalone together with the pinned main file, causes duplicate declarations. The delta requires the pinned main definitions `rowLE`, `Fminus`, `F`, `rows`, `masks`, `bits`, `target`, and `classification`.

Historical validation is retained without rerunning Lean. The standalone passed with a 5,500 MB memory cap and one Lean worker; the delta passed with a 3,072 MB cap and one worker. Their complete successful logs are `residual-orbits-standalone-5500.log` and `residual-orbits-bounded.log`. Each contains exact type and recursive axiom reports for `tables`, `row_properties`, `mask_cover`, `target_transport`, and `fourteen_targets`. The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`; `mask_cover` uses only the first and last. The audit-source bodies equal the distributed files, followed only by the commands in `audit-commands.txt` and whitespace. The historical exit codes and memory caps come from the original build record/handoff; the plain logs do not contain a separate process receipt. `residual-compact-final.log` retains the earlier classification audit.

`manifest.json` pins all packet file hashes, source sizes, the main revision, and audit-source provenance. `review.json` records source identity, scope, and independent review. `validation.txt` summarizes the existing checks. No fresh Lean or SAT run was made while preparing this packet.

This is a reusable classification and symmetry helper. It contains no circuit-to-residual extraction theorem, gate-count lower bound, or proof of the full posted gap L-meta-2373.
