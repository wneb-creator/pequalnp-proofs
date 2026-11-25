# L-meta-10760 proof and experiment backup

These files preserve completed work. No build or search was rerun while preparing this backup. `BACKUP-MANIFEST.json` records each successful experiment, the exact preserved source hash, and its complete stdout, stderr, and result metadata. Paths and commands in original result files retain their historical scratch locations.

## Validation status

- `Original10760.lean` is the exact source from upstream PR [16243](https://github.com/brilliant-hq/pequalnp-proofs/pull/16243), by MohamadEidAlAktaa. The full source passed `lake env lean --profile -j2` in 1286.97 seconds. This frontend/kernel compile did not itself run the repository checker or emit the named project's build products. The source is preserved unchanged for reproducibility and attribution; it is not claimed as a new proof authored by this pilot.
- The separately committed `Selected256.lean` candidate passed the named `lake build` in 1473.66 seconds under concurrent load. Its later repository-checker attempt ended with an infrastructure memory fault and **no verdict**. No file in this backup upgrades that result to acceptance.
- The extracted `AllScreenSelected.lean`, `AllScreenSelected128.lean`, and `AllScreenPoolOrdered.lean` programs each returned `TOTAL_BAD 0`, checking all 2655 used nodes across 22 grids and 82 primitive checks. These are compiled computational screens, not full kernel proof builds of the respective variants. Selected128 and PoolOrdered256 have not passed full kernel builds.
- The smaller `*Samples.lean` and `*Bench.lean` files are standalone computational definitions plus one or eight kernel-checked sample equalities. They do not prove the complete posted statement. These experiments examined literal states, staged normalization, precomputed domains, lookup order, plain `decide`, `rfl`, and related implementation changes. No tactic replacement demonstrated a useful overall speedup.

## Related preserved variants

- `../lower-bound/Selected128.lean`: projected coverage width 128; its independent complete computational screen is preserved here. Full kernel build remains pending.
- `../search/PoolOrdered256.lean`: only packed pool-index order changes; independently screened here. Full kernel build remains pending.
- `../lower-bound/Pruned.lean`, `FastData.lean`, and `FastDataGraph.lean`: exploratory full-source variants. Sample computations or narrower equality proofs do not establish full-source compilation.
- `../lower-bound/ForceSamples.lean`: checked constructor-forcing sample experiment; it did not show a speedup.

The original one/eight-node timing comparisons were performed under varying concurrent workload. Their recorded times are measurements, not controlled benchmark claims. Source status, full logs, and exact hashes take precedence over descriptions of intended optimizations.
