# Checker readiness for an actual L-meta-2056 candidate

Read-only inspection on 2026-11-25. No target checker run, verdict or new build is claimed. The current research partial must not be passed off as a proof of the posted statement.

The checked-in CLI is `node tools/check-lean.mjs <lean-file> <statement-file> check` (also supports `refute` and `reduce`). It builds the verifier, builds only the named module and `PEqualNP.Defs`, then checks the exact statement and permitted axioms with the compiled verifier. Exit 0 plus the final `ACCEPTED (check)` line is the successful verdict. Exit 3 is a checker fault, not a theorem verdict.

The shell currently has neither `lake` nor `elan` on PATH. `tools/bin/lake` locates the actual executable from `PEQUALNP_REAL_LAKE`, not from PATH. Therefore the plain checker command in the earlier handoff needs the environment below. `PEQUALNP_HOME` keeps queue state inside this job. The checker removes inherited `LEAN_*` variables; its queued builds take their thread count from `build-jobs.conf`. The verifier stage bypasses the queue and is not governed by that file.

After an actual candidate has passed independent full-boundary/model review, use the already reviewed generator from repository root:

```sh
python3 results/orch/plane-cegis/handoff/integrate_candidate2056.py \
  --input /tmp/oec/pequalnp-pilot-121/CANDIDATE.json \
  --output /workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_2056.lean \
  --statement /tmp/oec/pequalnp-pilot-121/statement-2056.txt \
  > /tmp/oec/pequalnp-pilot-121/candidate-handoff.stdout \
  2> /tmp/oec/pequalnp-pilot-121/candidate-handoff.stderr
```

The generator's exact template and statement comparisons currently pass. It accepts only strict backward binary AND/OR gates, checks all 756 complete boundary rows, refuses proof mode above 63 gates, and preserves all 32 separate 512-bit negative certificates. Its `--control64` mode does not append the posted theorem and must not be used for delivery.

After the parent renews the lease and schedules the build, from `/workspace/pequalnp-proofs/lean`:

```sh
LEAN_NUM_THREADS=1 /tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/lake \
  build PEqualNP.Outside.L_meta_2056 \
  > /tmp/oec/pequalnp-pilot-121/candidate-build.stdout \
  2> /tmp/oec/pequalnp-pilot-121/candidate-build.stderr
```

Only after that build succeeds, from `/workspace/pequalnp-proofs`, prepare the existing job queue and run the checker. These commands are a recipe; they were not executed during this audit.

```sh
mkdir -p /tmp/oec/pequalnp-pilot-121/build-queue
printf '%s\n' '1' > /tmp/oec/pequalnp-pilot-121/build-queue/build-slots.conf
printf '%s\n' '1' > /tmp/oec/pequalnp-pilot-121/build-queue/build-jobs.conf
PATH="/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin:${PATH}" \
PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/lake \
PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-121/build-queue \
PEQUALNP_REPO_ROOT=/workspace/pequalnp-proofs \
node tools/check-lean.mjs \
  lean/PEqualNP/Outside/L_meta_2056.lean \
  /tmp/oec/pequalnp-pilot-121/statement-2056.txt check \
  > /tmp/oec/pequalnp-pilot-121/candidate-checker.stdout \
  2> /tmp/oec/pequalnp-pilot-121/candidate-checker.stderr
```

Capture each actual exit status immediately, with complete stdout/stderr. The checker itself has a 30-minute per-process timeout; the parent must continue lease renewals. Do not bypass an existing check lock or edit the checker to obtain a result.

Observed prerequisites: Node v24.22.3; pinned Lake 5.0.0-src+611c117 / Lean 4.36.0; committed toolchain, manifest and lakefile unchanged; no `lakefile.lean` or `check.lock`; cached Mathlib.olean, Defs.olean, CheckLemma.olean and executable checklemma all present. The checker makes no direct network request and disables the shared artifact cache while retaining local built artifacts. No known offline blocker was found, but this inspection is not a successful checker run. Do not run `lake update` or rebuild Mathlib from source.
