# Independent review: TwoFilterSymmetry

Verdict: PASS for the exact auxiliary module. Reviewer: circuit_search, 2026-11-25T16:59:53.449126+00:00. No Lean build or source edit was made for this review.

Reviewed source SHA-256 `cc0dd981903a8dac90ba906a781c0f79e8984b1295c5361cc97c40fcb589dd5e`, 133 lines, 5,645 bytes. The automorphism table SHA-256 is `a552f667e7839ba5b5f289d06216b85765fdc765080568c61abf75834993a83a`.

The six ordered distinct pairs from {1,4,5} are all present. The conditional permutation definition agrees with every table row, sends the first member to1 and second to5, fixes0, and is bijective. I independently checked the15-edge set and all1,024 truth assignments for each permutation (6,144 total); results are in two-filter-automorphisms-independent.json. The Lean permutation_target statement has the same composition direction and all six pair guards. Cases outside those guards are not claimed to have these properties.

The generic rename acts only below10 and fixes every natural index at least10, including the free negative rail10, later gate wires, and invalid indices. Its injectivity proof covers all four below/above10 cases, so raw wires cannot collide with gate wires. rename_eq_wmap matches the library's11-to11 wire relabeling, with wire10 and out-of-range indices explicitly treated. This matters for preserving default-false reads as well as legal earlier-wire reads.

The seed equality includes the free complement at index10. seed_comp uses the required hypothesis that the permutation fixes0, ensuring the free input remains NOT(x0). eval_relabel then correctly proves eval(renamedD,x)=eval(D,x composed with permutation). It does not use the inverse permutation accidentally, and it does not require an undeclared ReadsBack assumption because the library relabeling theorem handles default reads.

The away bridge converts membership of the renamed variable back through injectivity, preserving absence in the complete input list. rails_preserved gives exact membership equivalence for {0,10}, with no new primary sent to0. reads_preserved consequently preserves ElimManyCount.reads gate by gate. This predicate scans every raw input-list entry, including any ignored NOT placeholder; it is not the separate effective-reader predicate that scans only a NOT head. The theorem is correctly scoped to the raw predicate. Equality of full gate-list counts follows from mapping and this pointwise equality; this module itself states the pointwise lemma, not a separate countP theorem.

Both original scratch files1884-two-filter-sym-second.stdout and.stderr were found and are empty. Exit0 is reported by the author; an empty diagnostic alone is not an exit-status proof. The JSON's historical scope label says construction/not-yet-Lean-checked, whereas the reviewed module now contains the finite Lean proofs; this stale historical label is not a mathematical inconsistency and should not be read as the current proof status.

No sorry, new axiom, native_decide, string literal, _root_ marker, or non-simp attribute appears. Only maxRecDepth and maxHeartbeats limits are set. The module supplies symmetry bridges for later branch assembly; it does not by itself exhaust or close the posted gap. Final single-file checker review remains separate.
