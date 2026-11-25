# Disk recovery and finite Hall cache

Status: repaired. Final filesystem free space was 742 MiB.

Initial emergency cleanup removed 2,957 regenerable Mathlib native C files (263,027,242 bytes) and temporarily compressed its cache executable. Every Lean artifact, dependency source, proof, search checkpoint, and log was retained. The cache executable was subsequently restored exactly (SHA256 253379b9758269d38f80239d274ef0fc6d0595944e0fabae5a1741999c5e5758), and its temporary gzip removed.

Lake metadata verification showed that Mathlib restoreAllArtifacts requires generated C files even for the elaboration facet. Accordingly, the initial deletion was fully repaired for the required dependency closure. No attempt was made to bypass artifact validation.

The closure was resolved with documented `lake --no-build -v build` commands for PEqualNP.Defs and Mathlib.Combinatorics.Hall.Finite. Preserved all 2,191 required Mathlib modules, the genuine Mathlib aggregator, cached checker, Cache modules, and other dependency packages. Removed only build artifacts of 749 unrelated Mathlib modules introduced by the broad Hall.Basic cache request, freeing 700,818,487 bytes. The complete path-and-size removal manifest is preserved as toolchain-recovery/2962-removed-cache-artifacts.json.gz. No source was removed.

Restored 2,190 required modules from exact official cache archives, with one already complete. Restoration recovered 177,375,419 bytes of generated C, using at most four concurrent curl/leantar jobs and deleting each downloaded archive only after successful extraction. Cache hashes came from the pinned Cache.Hashing implementation; its complete hash inventory, helper script, aggregate logs, and every individual download/extraction log are preserved in toolchain-recovery.

Final verification: `lake --no-build -v build PEqualNP.Defs Mathlib.Combinatorics.Hall.Finite` returned exit 0 and `All targets up-to-date (5149 jobs).` Complete stdout and stderr are preserved. No Mathlib source build ran. Normal named proof builds using these imports can now use the default artifact checks.

Hall.Finite itself was fetched from https://cache.mathlib.org/mathlib4-master/f/84671f9ea5a4327d.ltar. A Lean CLI test importing Defs and Hall.Finite and checking Finset.all_card_le_biUnion_card_iff_existsInjective' passed. Earlier lookup/fetch/extraction/test logs are in counting-logs.
