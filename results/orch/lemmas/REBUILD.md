# Rebuilding the preserved Lean artifacts

This source-closure audit covers 57 selected `.lean` modules in the pushed snapshot. Every nonproject/nonMathlib import of those selected modules resolves to a preserved source with exactly the matching module filename. There are no missing scratch-only imported modules and no cycles among these local imports. This audit did not rerun builds; existing complete compile logs record their original checks. Draft/conditional artifacts retain their original status.

`REBUILD-MANIFEST.json` records each source hash, import list, dependency order, the project pin hashes, and exact assembly recipes. Use the repository's pinned Lean/Mathlib environment and `PEqualNP.Defs`; do not update dependencies. In a fresh local build directory, preserve each source's basename, add that directory to Lean's module search path alongside the project paths supplied by `lake env`, and compile required local dependencies to same-named `.olean` files before their consumers. The manifest's order is a valid dependency order. No network, solver, credential, or search artifact is needed to compile these Lean modules after the pinned dependencies are cached.

These are independent historical artifacts, often containing the same frozen definitions. Do not import every file into one module or concatenate all full sources: that would redeclare overlapping namespaces. Build only the dependency closure of the artifact being reproduced. The cached helper import names are convenience module names, not names permitted in the final one-file PR; the reviewed inline packages remove those imports.

## Local module imports

| Source module | Preserved direct dependencies |
|---|---|
| CofactorCheck | SuccessorChecker |
| CompressedWireCut | IntermediateCopyCut |
| Expansion126663 | Expansion126663Conditional, SliceProfiles |
| Expansion126663Compact | CofactorCheck |
| Expansion126663CompactFinal | Expansion126663Compact, SliceProfiles |
| Expansion126663Conditional | CofactorCheck |
| IndexedForest | State4ReadOnceForest |
| IntermediateCopyCut | IndexedForest |
| PetersenEighteenExtension | PetersenSeventeenFull |
| PositiveCofactors | PetersenSeventeenFull |
| PositiveProfiles | PetersenSeventeenFull |
| RunPoolCut | PetersenSeventeenFull |
| SliceFromNine | PetersenSeventeenFull |
| SliceProfiles | PetersenSeventeenFull |
| State4Copy14 | SliceProfiles, RunPoolCut |
| State4ReadOnceForest | State4Copy14 |
| SuccessorChecker | PetersenSeventeenFull |
| WordCompression126663 | Expansion126663Conditional |
| ZeroProfiles | PetersenSeventeenFull |

All remaining modules import only `PEqualNP.Defs`, `Mathlib` or Mathlib submodules, except the explicit historical exception below. In particular, the large frozen prefixes such as `PetersenSeventeenFull`, `Live1024ReadOnceForest`, and `Live1024CertificateTower` are self-contained source snapshots; their earlier construction steps are not needed as imported modules.

## Historical target exception: GapBridge

`GapBridge.lean` imports `PEqualNP.Outside.L_meta_2373` as it existed when the bridge was compiled: the7156-line prefix preserved exactly as `PetersenSeventeenFull.lean`, SHA256 `67329ed982f00731191ac223c424eef83797b13cbe9cea474df3b9c6cacf5721`. The current target already contains the bridge declarations, so compiling this backup against that target would cause redeclarations.

To reproduce the historical modular build, use a fresh isolated module tree with the preserved prefix at `PEqualNP/Outside/L_meta_2373.lean`, compile its matching `.olean`, and place that tree before the current target on Lean's search path. Alternatively, make a standalone assembly by appending the body of `GapBridge.lean` after removing its first import line to the frozen prefix. Do not overwrite the current working target merely to rebuild the backup. The reviewed353344-byte target assembly also inserts `EighteenFullExtension.txt` between this prefix and the bridge; its exact recipe/hash are in the manifest.

## Compact subtree package

`Subtree126663CompactExtension.txt` is an append-only package for a prefix containing the seventeen/eighteen lower-bound helpers. It concatenates the bodies of `SliceProfiles`, `SuccessorChecker`, `CofactorCheck`, `Expansion126663Compact` and `Expansion126663CompactFinal`, in that order, removing only their initial import lines. The old literal-table package remains preserved separately. Both recipes are exact byte-checked; do not append both alternatives to one source, because they declare the same theorems.

`Expansion126663CompactFinal` and `Expansion126663` establish the same unconditional concrete subtree exclusion. `WordCompression126663` imports the old literal version only to compare its entire word list with the compact expressions. It is validation support, not an additional premise of the final theorem.

`FirstCopyRun`, `CopyInputPartition` and `CompressPartition` are small standalone checks with minimal repeated definitions. Their suffix files are incorporated unchanged into `IntermediateCopyCut` and `CompressedWireCut`; import the integrated consumers for further proofs rather than importing those standalone checks together.

## Snapshot exclusions

`Live1024Terminal0Closure.lean` is an obsolete, intentionally unpushed prototype with global resource options; use the checked localized `Live1024Terminal0.lean`. It is not promised by this frozen manifest, and no included module imports it. `WidthPrototype.lean` was included after its independent review passed; its sole import is `PEqualNP.Defs`. Later additions require a new manifest snapshot.
