# Checked L-meta-670 support sources

This snapshot contains the full custom Lean import closure of the checked Case159 proof, the literal binary bound, the tight formula endgame interface, and the finite proof tree child11. It also includes the compact Case159 alternative, the one-slack recurrence, the retained-input extension, and completed TightFirstData/0/1/2 batches. These are supporting results; this is not a complete proof of gap L-meta-670 and is not a submission-ready single-file PR.

`manifest.json` records every original path, source SHA256, custom/external imports, original compiled artifact SHA256 and timestamps. `SHA256SUMS` independently lists source hashes. `build-order.txt` is the complete topological build order. All 49 sources were copied byte-for-byte, rechecked against their originals, and every custom import resolves inside this bundle. The only external imports are `Mathlib`, `PEqualNP.Defs`, and `Batteries.Tactic.OpenPrivate`.

The modules preserve their original names. In particular, `Smoke` is the original `assembly/Smoke.lean`, not a later candidate with the same basename. Independent roots use distinct versions of the supporting framework; build each module separately in the listed order. Do not create an umbrella module importing every root, because those independent framework versions deliberately have overlapping declaration names.

## Toolchain and prerequisites

Use the pequalnp-proofs clone and its unchanged pinned `lean/lean-toolchain`, `lean/lake-manifest.json`, and `lean/lakefile.toml`. The pin is Lean 4.36.0; Mathlib is commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The verifier checks hashes for those files and `lean/PEqualNP/Defs.lean`. Do not run `lake update`. Restore the matching prebuilt Mathlib cache using `lake exe cache get` from the project's `lean/` directory, and ensure `PEqualNP.Defs` and its imports have their project build artifacts available. The bundle intentionally does not include the toolchain, Mathlib sources/cache, project definition sources, credentials, environment setup scripts, or old compiled artifacts.

## Verify and rebuild

From any directory, pass the actual pinned project's `lean/` path:

```sh
python3 /path/to/checked-bundle/rebuild.py --lean-dir /workspace/pequalnp-proofs/lean --verify-only
python3 /path/to/checked-bundle/rebuild.py --lean-dir /workspace/pequalnp-proofs/lean
```

To rebuild only one result and its transitive dependencies:

```sh
python3 /path/to/checked-bundle/rebuild.py --lean-dir /workspace/pequalnp-proofs/lean --root Case159Closed
```

Repeat `--root` to select several results. The script verifies hashes, sets the custom module path only for child processes, and invokes `lake env lean -R <modules> -o <module>.olean <module>.lean` in exact dependency order. It saves complete stdout and stderr to `rebuild-logs/<module>.log`, stops at the first failure, and writes resulting `.olean` files beside the sources. Compilation may take several minutes. To resolve one source timestamp discrepancy, only Smoke was recompiled against its existing checked base while creating this snapshot; the expensive base certificate was not rebuilt.

## Checked scope

- `Case159Closed` and `CompactCase159Test` prove the same closed exclusion of the specific Case159 state at budget 13 with two NOT gates.
- `LiteralBinaryTest` proves the structural bound excluding all target size-15 cases with at least six NOT gates.
- `TightFormulaEndgameTest` supplies a checked endgame reduction with explicit finite-check assumptions; TightFirst0/1/2 supply only their own completed finite batches.
- `FiniteProofTreeChild11` checks the one named child case, not all leaves.
- `SlackOneTest` proves soundness of the one-slack recurrence, with no assertion that all remaining finite instances have passed.

The source bodies include development-only imports, `#print` commands, and private-name bridges where needed by the historical module layout. They must be integrated and cleaned before the separate one-file contribution checker can accept a full proof.

## Provenance note

All original `.olean` artifacts were present at snapshot time. `Smoke.lean` had been regenerated 48 seconds after its original successful compilation, so its exact current source was recompiled against the existing checked SlimCompact1007 module. A fresh Smoke artifact was emitted at 2026-11-24 00:30:58 UTC; the complete compiler output is in `provenance/smoke-recheck-20261124.log` and has warnings but no errors. The manifest retains both old and new Smoke artifact hashes. Every bundled source timestamp now precedes its recorded compiled artifact. These artifacts were not copied into the bundle: run the rebuild on the restored workspace to recreate them.

## Versioned additions

This version adds the checked source closures rooted at: FirstOrbitTest, UnorderedPairsTest, UnorderedFormulaTest, SlackCutsTest, UnorderedEmbeddingTest, TightLowerEleven, UnorderedEndgameTest. The earlier archive remains unchanged. All new module source timestamps precede their compiled artifacts, and their source bytes were rechecked after copying. The manifest records the prior bundle manifest hash.

The added `TightLowerEleven` root discharges all324 finite cases using TightFirst0 through TightFirst8 and proves the closed bound of at least11 binary gates, hence excludes size15 target cases with at least5 NOT gates. `UnorderedEndgameTest` remains conditional on its24 explicitly stated representative one-slack checks; no completed NOT≥4 claim follows from that module alone.

## Versioned additions

This version adds the checked source closures rooted at: UnorderedFirst01Closed. The earlier archive remains unchanged. All new module source timestamps precede their compiled artifacts, and their source bytes were rechecked after copying. The manifest records the prior bundle manifest hash.
