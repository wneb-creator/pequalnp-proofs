# Finite table review guide

The full candidate is `lemmas/union_prune_all_chunks.lean`. It is a supporting result, not a proof of L-meta-2592.

- The six singleton masks are 1, 2, 4, 8, 16, 32.
- The four target masks are 22, 37, 25, 42, corresponding to bce, acf, ade, bdf.
- `helperMasks_spec` checks that the 53 allowed helpers are exactly the nonempty nonsingleton masks below 64 that are not targets.
- `setStepAllowed` permits a target set when it is a subset of an available set, or the union of two available sets. Pruning is deliberately more permissive than actual Boolean gates.
- `closeStarSets` makes up to seven passes over the seven possible added sets: four targets and three helpers. Existing sets are not duplicated. A pass with no addition terminates.
- Each pair lemma checks all third helpers larger than its second helper. Each row uses only second helpers larger than its first helper. The final search therefore covers all 23,426 unordered triples of distinct helpers.
- The 1,378 pair lemmas use `decide +kernel`; row and final assembly use Boolean rewriting. There is no external certificate or native evaluation.

The file does not yet prove that every seven-operation set program maps into this closure, nor that an arbitrary one-NOT circuit maps into a seven-operation set program. Those are separate semantic bridges. Therefore the direct formal conclusion is exactly `starHelperSearch = false`, not a circuit-size bound.

Independent C++ and Python implementations also returned no witness, and a four-helper positive control generates all targets in eight operations. Those checks are corroboration; Lean kernel evaluation is the proof of the stated Boolean result.
