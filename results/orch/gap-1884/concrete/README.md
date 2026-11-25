This checkpoint proves ordinary Petersen non-NOT count at least17, canonical free-NOT size18 paid-NOT count at most1, and vertex-deleted Petersen non-NOT count at least15. These are unconditional helper results, not the full assigned L-meta-1884 statement. The existing source was developed before lease invalidation and its final unchanged validation passed after the pre-existing base build finished. Independent final-wrapper review: status_review and root. No posted-statement checker acceptance is claimed.

From lean/ with the prepared toolchain active:

```sh
lake env lean --root=../results/orch/gap-1884/concrete -o ../results/orch/gap-1884/concrete/SignedFloorBase.olean ../results/orch/gap-1884/concrete/SignedFloorBase.lean
lake env bash -c 'LEAN_PATH="../results/orch/gap-1884/concrete:${LEAN_PATH}" lean ../results/orch/gap-1884/concrete/PetersenConcrete.lean'
```

Full compiler stdout/stderr is preserved. The source depends only on Defs after inlining the base; cached imports are used here solely to avoid rechecking the large accepted finite certificate for every helper.
