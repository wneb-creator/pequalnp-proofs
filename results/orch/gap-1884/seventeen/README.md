The new theorem `circuit_nonNot_seventeen1884` proves that a Petersen circuit has at least 17 non-NOT gates, conditional on the signed lower bound 15 for the nine-variable vertex-deleted graph. That premise is the already checked `nineFloor` in L_meta_6581. This checkpoint does not prove the assigned L-meta-1884 statement.

Core contains the generic signed-circuit machinery copied from L_meta_6581, with its original attribution and Apache-2.0 comments retained. Extra contains the new first-gate retention and ten finite projection arguments. The full source checks passed with exit 0; the saved files contain complete stdout and stderr. Core has one attribution-only comment added after that successful check.

From `/workspace/pequalnp-proofs/lean`, with the prepared Lean toolchain active:

```sh
lake env lean --root=../results/orch/gap-1884/seventeen -o ../results/orch/gap-1884/seventeen/SemanticBudgetCore.olean ../results/orch/gap-1884/seventeen/SemanticBudgetCore.lean
lake env bash -c 'LEAN_PATH="../results/orch/gap-1884/seventeen:${LEAN_PATH}" lean ../results/orch/gap-1884/seventeen/SemanticBudgetExtra.lean'
```
