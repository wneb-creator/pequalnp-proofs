This branch preserves partial research for pequalnp-pilot-92. It is not a single-file proof PR: the exact posted theorem is absent.

The self-contained checked sources are `lean/PEqualNP/Outside/L_meta_2592.lean` and `lean/PEqualNP/Outside/L_meta_1886.lean`. Use the pinned toolchain and dependencies in `lean/lean-toolchain` and `lean/lake-manifest.json`. With enough storage, fetch the official prebuilt cache before building; never run `lake update` or rebuild Mathlib from source.

```sh
cd lean
lake exe cache get
lake build PEqualNP.Outside.L_meta_2592 PEqualNP.Outside.L_meta_1886
```

Complete successful logs are `partial17-build.stdout` and `partial1886-v2-build.stdout`, with separate stderr files. The v2 manifest and independent review identify its exact source hash and all appended components. Axiom reports are preserved alongside the build logs.

`lemmas/mono_nine.lean` is a separate self-contained extraction of the checked L_meta_8367 monotone certificate, with a new lower16 wrapper. Its source manifest, independent review, final build logs, and standard-three axiom report are preserved. `lemmas/mono_nine_bridge.lean` transfers it to the shared nine-variable framework and derives the actual-circuit floor. Smaller research files use sibling module names as compile harnesses; their matching basenames must be compiled in dependency order on a common Lean search path. Plain `.fragment.lean` files omit those harness headers. Do not submit scratch imports, private-export bridges, or these multiple artifacts as a proof PR.

The endpoint-NOT work is in `constant_sweep_mono`, `constant_not_cut`, `endpoint_order`, `endpoint_consumers`, `endpoint_restrict`, and `endpoint_lower0`. The final lower theorem takes the now-checked actual-nine bound as an explicit premise. Unused-NOT semantic and compiler helpers are separate; their final circuit wrapper was not written before lease withdrawal.

The official checker attempt and its environment fault are in `checker1886.stdout`/`.stderr`; `checker-environment-feasibility.txt` explains the missing umbrella cache and storage limits. Passing the named partial build does not prove the exact gap statement.

All search archives include exact scope, controls, complete logs, and independent reviews. None contains a valid Petersen counterexample. `validation.txt` is the current status snapshot; `NOTES.md` and `TIMELINE.md` retain the detailed research history. Published Git history retains earlier checkpoints and source versions.
