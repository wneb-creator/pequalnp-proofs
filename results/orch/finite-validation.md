# L-meta-3178 independent finite validation

UTC run: 2026-11-25 00:34:56.784506 through 00:34:58.193321.

Result: PASS. This validates the proposed structural reduction's elementary bridge; it does not exhaust the circuit space or prove the two lower-bound hypotheses.

- All 100 pairs of indices in 0..9 were filtered by the posted pin hypotheses. Exactly 16 survived: [0,k] and [k,0] for k=1..8.
- Exhaustive checks on all 512 inputs and all 16 pin lists verified that the extra OR bit equals x0 OR xk: 8,192 checks.
- 57 suffix circuits covered sizes 0..13 and additional empty-arity, one-input, repeated-input, forward-reference, and absent-output cases. All assignments and legal pin lists verified equality between suffix evaluation on the augmented bank and full evaluation after prepending NOT x0 and OR pins: 466,944 checks.
- 912 prefix-count checks confirmed full size = suffix size + 2, full NOT count = suffix NOT count + 1, full non-NOT count = suffix non-NOT count + 1, and preserved fan-in-two legality.
- All 105 possible (size, NOT-count) pairs with size at most 13 verified that 13 <= full non-NOT count implies suffix NOT count <= 1.

Independent graph checks: all vertices are essential; 454 of 512 assignments are positive. Independence number is four. Minimum vertex covers are {1,2,4,5,8}, {0,2,3,5,6}, and {0,1,3,7,8}. An explicit monotone 16-gate star-cover circuit was verified on every input. There are 12 maximal independent sets.

The stabilizer of vertex 0 has only the identity and [0,5,8,3,4,1,7,6,2]. It has five nonzero vertex orbits: {1,5}, {2,8}, {3}, {4}, {6,7}. Existing reductions R_meta_3178_1 and R_meta_3178_31 already use this symmetry, so it is not a useful new cut by itself.

Artifacts:
- finite-analysis-validate.py: deterministic validation program (seed 3178).
- finite-analysis-validate.log and finite-analysis-validation.json: complete run output.
- finite-analysis.json: symmetry computation.
- finite-analysis-checks.json: graph statistics and verified upper-bound circuit.

Recommended new cut: first require the generic Petersen lower bound of 13 non-NOT gates; second require nonexistence of the posted suffix circuit when its NOT count is at most one. Prepending the two fixed gates bridges these independently meaningful stages. The already checked parent L_meta_2758 implements this bridge in its noPair2758 lemma, and its non-NOT lower-bound proof provides evidence that the first component is true.
