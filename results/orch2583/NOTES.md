# L-meta-2583 orchestration notes

New own lease received 2026-11-25 14:52:34 UTC, expires 15:12:34 UTC.
Reductions closed. Exact statement in scratch statement-2583.txt.
Old L-meta-2592 work stopped after lease410 and preserved at commit9b9d9f1a.

## Toolchain/checker feasibility (2026-11-25 14:55 UTC)

No supported definitions-only checker mode exists: all three modes import full Mathlib unconditionally. Even a generous cleanup estimate including all unrelated scratch/results, static/editor/source toolchain files, and other Outside sources leaves 2,690,915,208 bytes short. No live cache or toolchain changes were made. The existing upstream PR authoritative workflow is the genuine remaining checker path. Details: `results/orch2583/toolchain/feasibility.txt`.

## reduction_strategy 2026-11-25T14:57:31.347851+00:00

Checked `SingleLevelChecked.lean`: for every finite simple graph G, IsAO2 n C, TopForm G C, and junk G C = empty imply ReadK.IsReadK n C 1. No leastness/correctness/no4cycle/plane assumptions required. Pure OR-only operand wires yield unit proof vectors and singleton witnesses. Every AND is below graphFun, hence cannot accept a singleton, forcing distinct leaf units. TopForm with empty junk supplies no nested AND cones. The unresolved part of L-meta-2583 remains finding a no-larger circuit with empty junk (or proving another route to read1). Copied read-vector infrastructure from checked L7684 and cone recurrence from L8385, then proved new generic bridge. Lean check exit0 with empty stdout/stderr.
