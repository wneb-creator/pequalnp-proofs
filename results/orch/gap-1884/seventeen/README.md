The new theorem `circuit_nonNot_seventeen1884` proves that a Petersen circuit has at least 17 non-NOT gates, conditional on the signed lower bound 15 for the nine-variable vertex-deleted graph. That premise is the already checked `nineFloor` in L_meta_6581. This checkpoint does not prove the assigned L-meta-1884 statement.

Core contains the generic signed-circuit machinery copied from L_meta_6581, with its original attribution and Apache-2.0 comments retained. Extra contains the new first-gate retention and ten finite projection arguments. The full source checks passed with exit 0; the saved files contain complete stdout and stderr. Core has one attribution-only comment added after that successful check.

From `/workspace/pequalnp-proofs/lean`, with the prepared Lean toolchain active:

```sh
lake env lean --root=../results/orch/gap-1884/seventeen -o ../results/orch/gap-1884/seventeen/SemanticBudgetCore.olean ../results/orch/gap-1884/seventeen/SemanticBudgetCore.lean
lake env bash -c 'LEAN_PATH="../results/orch/gap-1884/seventeen:${LEAN_PATH}" lean ../results/orch/gap-1884/seventeen/SemanticBudgetExtra.lean'
```

`PaidNotOne.lean` adds the canonical free-NOT consequence: a size-at-most-18 circuit computing Petersen on the ten raw inputs plus the free complement of input 0 has at most one actual NOT gate. The signed nine-variable lower bound remains an explicit hypothesis. This source compiled with exit 0; full logs are `paid-one.stdout` and `paid-one.stderr`. The delta was independently reviewed by both the semantic and ledger agents.

To compile this dependent component, first emit the Extra artifact, then check the wrapper:

```sh
lake env bash -c 'export LEAN_PATH="../results/orch/gap-1884/seventeen${LEAN_PATH:+:${LEAN_PATH}}" && exec lean --root=../results/orch/gap-1884/seventeen -o ../results/orch/gap-1884/seventeen/SemanticBudgetExtra.olean ../results/orch/gap-1884/seventeen/SemanticBudgetExtra.lean'
lake env bash -c 'export LEAN_PATH="../results/orch/gap-1884/seventeen${LEAN_PATH:+:${LEAN_PATH}}" && exec lean --root=../results/orch/gap-1884/seventeen ../results/orch/gap-1884/seventeen/PaidNotOne.lean'
```
