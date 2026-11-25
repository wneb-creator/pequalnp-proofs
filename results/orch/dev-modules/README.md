# Preserved fast Lean modules

These are the exact modular source variants used for the successful development builds. Some same-named files in `../lemmas/` are standalone harnesses with dependencies inlined; they must not replace these modular versions.

All nine modules listed below had successful Lean checks before the lease pause. `PetersenBinary17.petersen_binary_lower17_of_table` still has an explicit `SignedFloor.Lower true inputs graph 15` hypothesis. The nine-input finite certificate is checked separately in `../lemmas/SignedFloor.lean`; its table-bound adapter is written but was not checked before the pause. This is partial progress, not a proof of the posted gap.

## Original build invocation

The existing Mathlib cache and `PEqualNP.Defs.olean` were already prepared. Working directory was `/workspace/pequalnp-proofs/lean`. Each module was checked with this command form; the original source paths are recorded in `manifest.json`:

```sh
PATH=/tmp/oec/pequalnp-pilot-108/toolchain/lean-4.36.0-linux/bin:$PATH \
LEAN_PATH=/tmp/oec/pequalnp-pilot-108 \
lake env lean -R SOURCE_ROOT \
  -o /tmp/oec/pequalnp-pilot-108/MODULE.olean \
  SOURCE_ROOT/MODULE.lean > BUILD.stdout 2> BUILD.stderr
```

For scratch sources, `SOURCE_ROOT` was `/tmp/oec/pequalnp-pilot-108`. For `FullRun` and `PetersenBinary17`, it was `/workspace/pequalnp-proofs/results/orch/lemmas`. The module names and valid sequential build order are:

1. SignedCore
2. Structural
3. OperandRetentionFast
4. FullRunLower17
5. ReachRestriction
6. MiniNine
7. FullRun
8. PetersenBinary17
9. NonOrLower18

`NonOrLower18` is an additional checked branch theorem and is not required by `PetersenBinary17`. Independent prerequisites were sometimes built concurrently; the order above satisfies every import dependency.

## Rebuild from these copies

The following shell commands reproduce the modular checks using the preserved copies. They have been documented, not rerun after the lease pause. This assumes the pinned Lean toolchain, warm cache, and checked `PEqualNP.Defs` from the original job. It never runs `lake update` or builds Mathlib from source.

```sh
cd /workspace/pequalnp-proofs/lean
export PATH=/tmp/oec/pequalnp-pilot-108/toolchain/lean-4.36.0-linux/bin:$PATH
export LEAN_PATH=/tmp/oec/pequalnp-pilot-108/rebuild-modules
mkdir -p /tmp/oec/pequalnp-pilot-108/rebuild-modules
for module in SignedCore Structural OperandRetentionFast FullRunLower17 ReachRestriction MiniNine FullRun PetersenBinary17 NonOrLower18; do
  lake env lean -R /workspace/pequalnp-proofs/results/orch/dev-modules \
    -o "/tmp/oec/pequalnp-pilot-108/rebuild-modules/${module}.olean" \
    "/workspace/pequalnp-proofs/results/orch/dev-modules/${module}.lean" \
    > "/tmp/oec/pequalnp-pilot-108/rebuild-modules/${module}.stdout" \
    2> "/tmp/oec/pequalnp-pilot-108/rebuild-modules/${module}.stderr" || exit "$?"
done
```

These temporary module imports are for development reproducibility; final submission rules require a single consolidated source file with permitted imports.
