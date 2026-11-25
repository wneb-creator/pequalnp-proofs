# Checker cache capacity analysis

No files were deleted and no artifacts were downloaded during this analysis.

The unmodified checker imports the entire pinned Mathlib before the proof. CheckLemma.lean:351–356 explicitly calls importModules for Mathlib plus Defs with trustLevel 0/loadExts true. Mathlib.lean directly imports all 8712 Mathlib modules plus Std and Batteries. Of these 8712 modules, 2189 are cached and 6523 are missing (the root Mathlib module is separate).

Required Lean 4.36 import artifacts are .olean, .olean.server, .olean.private, .ir.sig and .ir. Environment.lean:2443–2456 reads both olean siblings unconditionally for module-system files; lines2458–2469 read IR and signature together. The checker uses the default private import level, which loads transitively at that level (lines2547–2555). Removing .olean.server as supposedly optional is NOT safe on this version.

Present allocated sizes (MiB, 4096-byte filesystem block allocation):

| Package | Required import artifacts MiB | .ilean MiB | generated .c MiB | static .a MiB |
|---|---:|---:|---:|---:|
| batteries | 60.8 | 1.6 | 14.5 | 0.0 |
| proofwidgets | 8.5 | 0.2 | 2.4 | 0.0 |
| importGraph | 27.0 | 0.7 | 8.4 | 0.0 |
| plausible | 9.3 | 0.2 | 3.1 | 0.0 |
| aesop | 92.3 | 2.2 | 31.8 | 0.0 |
| Qq | 15.1 | 0.3 | 4.8 | 0.0 |
| LeanSearchClient | 3.6 | 0.1 | 1.1 | 0.0 |
| mathlib | 1553.6 | 78.5 | 175.5 | 0.0 |
| toolchain | 2097.8 | 91.0 | 0.0 | 407.5 |

Available disk at measurement: 650.5MiB. Toolchain total3112.5MiB, currentMathlib build total2001.5MiB, allLake tree2807.0MiB. Genuine cached compressed archives occupy154.1 MiB (2481 files).

Safe cleanup candidates:

- Toolchain .ilean:91.0 MiB; not read by importModules and not required for these command-line elaboration/checking jobs.
- Toolchain static .a archives:407.5 MiB, only after all required executables have linked and no relinking is needed. ldd confirms Lean/Lake use shared libraries at runtime. Keep all shared libraries and compiler tool support needed for future links.
- Already-unpacked cache archives:154.1 MiB; reproducible, but a later full cache get may download them again, so this is not guaranteed net working headroom.
- The119.2 MiBcache executable can be discarded only after all download/unpack work is finished, not while using cache get.

Do NOT delete .ilean or generated.c files from existing cached Mathlib/dependency builds as a routine cleanup while retaining normal Lake build flow. Lake Build/Module.lean:914–929 explicitly checks these artifacts; deletion can invalidate a cached module and provoke restoration orrebuilding, contrary tothe task’s rule against building Mathlib from source. They are unneeded by direct Lean import but not optional for Lake’s module build checks.

Size estimates for the missing full Mathlib cache:

- UNVERIFIED by exact remote artifact sizes: 4597.7MiB additional required import artifacts, extrapolating cached required bytes per module.
- UNVERIFIED by exact remote artifact sizes: 3947.0MiB additional required import artifacts, extrapolating cached required bytes per source byte.
- These estimates exclude optional generated C/ilean/hash files and download working headroom. Current cached Mathlib requiredartifacts are measured exactly; missing artifactheaders are unavailable locally.
- Theofficial local Mathlib cache implementation has per-module hash addresses, not an available unpacked-size manifest. Existing LTAR header contains only magic and depHash (Cache/IO.lean:454–469); theofficial root Mathlib.trace lists output hashes but no output sizes. leantar 0.1.20 help provides noentry-selection orsize-listing option.

Even the aggressive final cleanup above adds only~772 MiB to~650 MiB available, leaving~1.4 GiB, while both observed-data extrapolations need3.85–4.49 GiB just for missing required artifacts. There is no supported safe cleanup plan that establishes that the full cache fits. Do not start a blind full cache fetch. The concrete blocker is the 7.9 GiB execution volume together with the unmodified checker requiring full Mathlib; exact additional remote artifact size is unverified. A materially larger volume (roughly 12 GiB total as a planning estimate) is needed to attempt the full cache without filesystem/quota tricks.

Repository workflow review: authoritative requires an existing PR and dispatch from the base default branch; advisory runs on PR events. No suitable pre-PR remote check was dispatched. The checker source/configuration was not changed.
