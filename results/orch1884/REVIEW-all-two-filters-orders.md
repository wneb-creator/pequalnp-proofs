# Independent review: AllTwoFiltersOrders

Verdict: PASS. Reviewed by circuit_search on 2026-11-25T17:01:01.208230+00:00. Exact source: SHA-256 `bc945f14e6edb873f6c9680ffa2dea398a4409f6e43ea49726865970188bbe30`, 51 lines, 2,891 bytes. No source edits or new compilation were made.

The and_step lemma proves equality of the entire updated wire list for either ordering of an AND gate's two operands. It uses Boolean commutativity and the exact List.all semantics, so it works for any incoming wire list, including default-false reads. It does not assume the two operands are distinct or that reads are backward.

The wrapper accepts either order independently for each of the two designated filters. The conjunction of those two disjunctions covers all four operand-order combinations. The full list fold is expanded across the same prefix/intermediate/suffix gate lists, and each filter step is rewritten locally. Gate count, output index, paid-NOT position/output wire11+pre.length, all other gates, and source indices remain identical. There is therefore no renumbering or output-offset issue.

The equality he is oriented original evaluation = canonical-order evaluation. The final he.symm.trans(hcompute x) correctly obtains canonical-order evaluation = target for AllTwoFilters.impossible. Every structural assumption of the imported theorem is passed explicitly and unchanged: ordered distinct neighborsv,w from{1,4,5}, monotone fan-in-two remaining gates, absence ofv/w in those gates and the NOT operand list, output exclusion, sizeatmost18, and at leasttwo raw rail readers among the remaining gates.

The reader predicate is the same ElimManyCount.reads raw input-list predicate reviewed in TwoFilterSymmetry. This wrapper does not replace it with effective NOT-head-only counting and does not establish the reader-count hypothesis. It only removes the operand-order convention for the two given filters. The global classification needed for L-meta-1884 remains outside its statement.

I inspected the original stdout/stderr files1884-all-two-orders-second.*. Stderr is empty. Stdout contains one benign unused-simp warning for Bool.and_true at line15; there is no error text. Exit0 is reported by the author and was not rerun in this review. The source contains no sorry, new axiom, native_decide, string literal, _root_ marker, attributes, or option settings. AllTwoFilters itself is being independently reviewed by counterexample; this review checks this wrapper against its exact visible contract and does not replace that dependency review.
