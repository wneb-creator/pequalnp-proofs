# Rebuilding the checked auxiliary 14-gate theorem

Run from a checkout containing these committed sources, with the pinned Lean/Lake toolchain available:

```sh
bash results/orch1884/rebuild-auxiliary14.sh
```

The optional first argument selects a log directory. The default is `results/orch1884/rebuild-logs`. If `lake` is not the real installed executable, set `PEQUALNP_REAL_LAKE` to the absolute path of the installed Lake binary. No container-specific installation path is embedded in the script.

The script retrieves the pinned Mathlib binary cache, builds the listed project helper modules, and exports twenty short-name modules in dependency order. It never runs `lake update`. It explicitly sets `LEAN_PATH` to this checkout's `results/orch1884/lemmas` directory and uses `lean --root` with that same directory; these steps are required because the scratch modules are outside the ordinary `lean/PEqualNP` tree. Each invocation saves its entire stdout and stderr separately. A failing command stops the script.

The longest export is `GeneralReaderStandalone`, which contains the two previously checked finite lower-bound certificates. Every later export reads its `.olean`; it does not recompile that certificate. Rebuilds need the repository's pinned Mathlib cache. If cache retrieval fails, fix the cache/toolchain setup before proceeding rather than building Mathlib from source.

The exact dependency order and source SHA256 values are recorded in `auxiliary14-dependencies.json`. The order is also explicit in the script. Project helpers are ordinary checked repository modules, built by Lake before the short-name exports; their own dependencies are resolved by Lake from the pinned checkout.

The final module is `RelaxationFloor.lean`, theorem `PEqualNP.Outside.L_meta_1884.RelaxationFloor.fourteen`. Its proved statement is: every `Monotone2` circuit on nine inputs satisfying the twelve positive and thirteen negative rows from `StrongRelaxRows` has size at least fourteen. It places no assumptions on minimality, backward reads, gate liveness, or the number of input readers; those properties are obtained inside the proof.

The script ends by asking Lean for the theorem's axiom dependencies. The recorded successful result is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This is a reproducible intermediate theorem, not a submission of the posted L-meta-1884 statement. The short-name and helper-module imports must be resolved into the permitted single-file format before a posted-theorem PR can be checked. See `relaxation-floor-proof.md` for the successful compilation record, proof outline, and exact row list.

The rebuild script was checked statically against every source import and with `bash -n`. Its individual compilation/export commands and project-helper builds have already succeeded in this session. The entire script was not rerun after authoring, to avoid repeating the large certificate build.
