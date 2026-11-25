# Independent search review

Reviewer: status_research. Date: 2026-11-25 UTC.

Reviewed snapshots:

- `counterexample_search.cpp`: SHA256 `49a60d5287b18d98631bcffabda611b3922a5153dd39fd03695c3e9b63711a74`.
- `counterexample_sat.cpp`: SHA256 `a963963ca430b57607a04e87d1833511b490a4f30285a3fdeac3de626b78f114` (includes the 1–4 NOT cap and optional ordered predecessor constraint).
- Also inspected the local repair loader and the author's encoding controls.

## Verdict

No false-positive witness defect found in either main search. Suitable as exploratory checkpoint code. Neither an unsuccessful heuristic search nor UNSAT in a restricted SAT variant proves the posted Lean statement.

## Target and witness semantics

- Both sources list exactly the posted 15 Petersen edges on inputs 0 through 9.
- Independent enumeration gives 948 true assignments and 76 false assignments. The false assignments have size distribution 1, 10, 30, 30, 5 for cardinalities 0 through 4.
- Stochastic evaluation uses 16 words of 64 bits, covering exactly all 1024 assignments; no unused high bits enter its score.
- Every generated predecessor is below the new gate's wire index. The stochastic circuit has exactly 19 gates, and the last gate is its output.
- Stochastic score zero is a valid full truth-table match for any positive false-positive weight. If `PNP_REQUIRE_NOT` is present, score zero additionally requires a NOT gate. Without it, a NOT-free 19-gate match would not directly satisfy the assigned gap's NOT premise.
- The 20-gate seed cover is valid. Deleting one gate and replacing its uses by one of its earlier operands preserves well-founded wiring.
- The stochastic `best` score mixes different false-positive weights between restarts. It is a weighted objective, not one consistent Hamming-error count; this does not invalidate a zero score.

## SAT encoding

- Gate operation and each operand selector are exactly one-hot.
- Guarded clauses express AND, OR, and NOT truth tables correctly.
- Selected input values and prior gate values are linked to operand values correctly for each sampled input.
- Binary operand order is canonicalized; NOT's ignored right operand is fixed to wire zero.
- Mode 0 excludes NOT; mode 1 requires exactly one NOT; other modes require at least one and prohibit any five NOT gates, giving 1–4 NOTs.
- Optional `PNP_ORDERED` constrains maximum predecessor indices to be nondecreasing. Its high-index variables correctly select the left operand for NOT and the canonical right operand for binary gates.
- CEGIS starts with all independent inputs and all size-two inputs. Every candidate is evaluated independently on all 1024 assignments, and a witness file is written only when none disagree.
- SAT result 20 certifies only this encoding. The source syntax omits empty operands, constant gates, invalid reads, and arbitrary output positions. Formal normalization and any symmetry justification are separate proof obligations. No full-statement UNSAT claim is justified by this search alone.

## Controls

Independent reviewer control source and complete output are in scratch `sat-review-control.cpp` and `sat-review-control.stdout`:

```text
known_cover_gates=20 known_cover_mismatches=0
model_mismatches=0
locked_positive_result=10
locked_wrong_output_result=20
```

The positive control locks the known monotone cover circuit and constrains all 1024 assignments. The negative control changes its final OR to AND. Both passed. The author's separate controls were inspected and also passed: 20-gate monotone, 21-gate unused-NOT, 22-gate double-NOT, and a mutated negative circuit. Complete logs remain in scratch.

The repair loader initially canonicalized binary operands but not a NOT gate's ignored right operand. Fixing a stochastic NOT with a nonzero ignored operand would create artificial UNSAT assumptions, because the SAT encoding requires that operand to be zero. This was reported to the author; the then-current seed had no NOT, so that run was unaffected. The author's earlier binary-order bug was already fixed and the failed exploratory logs were retained.

## NOT comparability check

Let `g0 <= g1` pointwise and `f = if h then g0 else g1`. Then:

- If `h <= f`, replacing the NOT output by true gives exactly `f = g1`.
- If `f <= h`, replacing the NOT output by false gives exactly `f = g0`.

This follows pointwise and does not need monotonicity in the original input variables. An independent bounded enumeration checked every pair `g0 <= g1` and every `h` on an eight-point domain: 1,679,616 cases, zero counterexamples; each implication's premise held in 65,536 cases. Constant propagation and the resulting gate-count decrease still require a formal circuit lemma before this can justify a complete lower-bound proof.
