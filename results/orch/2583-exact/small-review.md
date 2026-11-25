# Independent small-graph SAT and five-line prefix review

Verdict: PASS as finite computational search and candidate validation, pending any eventual Lean certificate.

Reviewed `small_nested.py` SHA256 `17b8c54706c93256c80b5a564dcf621a7607d29bc4693c6655fa885e909e5201` and `five_lines.py` SHA256 `71d7176ffc6eb7eeb388bf94ece4ebdc8258bdb16919d83c8b607bf4be7d0d08`.

The current small encoder allows equal operands and uses one-hot selectors over earlier wires. AND/OR clauses and mux signs are correct. Every non-output gate must feed a later gate, so every gate reaches the final output. The lexicographic order (maximum fanin, minimum fanin) is a valid representative ordering for unseeded DAGs: greedily choose the smallest ready pair, and newly ready children have a larger maximum. The optional nested-AND witness computes ordinary ancestor reach and requires two AND gates on one path; it is disabled by --allow-flat in the three strict-saving runs. With that flag, a smaller active circuit can be padded by AND(output,output) gates and then canonically ordered, so exact gate count is not an additional restriction on ≤budget circuits.

The boundary basis enumerates every subset of the line side, takes all compatible points, and retains the maximal line closure. With the checked bipartition/disjointness/full-input assertions, these are exactly the maximal false inputs; minimal true inputs are edge pairs. Monotonicity makes this basis complete. After SAT, the model is reevaluated using full 2^n-row bit tables, independently of basis completeness. The little-endian input-table construction was checked at boundary bit positions; its periods and byte counts are correct. Activity and optional nested status are also rechecked on the decoded model.

The five-line classification canonicalizes the multiset of point neighborhoods under all 120 line permutations. This is exactly bipartite graph isomorphism with fixed side roles; it need not be induced by a projective-plane automorphism. All 1,287 five-line subsets are partitioned into classes of 117, 702 and468. Omitting points incident with none of the chosen lines is harmless for this subfunction.

Equal point-neighborhood groups can be replaced by one OR input because they occur on exactly the same line side. The prefix cost is sum(|group|−1), namely4/1/0. Independently substituting these group ORs into each compressed edge function matched the uncompressed truth table on all262,144/131,072/65,536 assignments respectively. The target compressed gate counts19/22/23 therefore lift to23 gates on the selected five lines, compared with the24-gate star construction. Adding the eight other four-gate line stars and eight final OR gates would give63 gates for the entire q3 plane.

UNSAT is restricted to the model with these fixed OR prefixes; it does not exclude general five-line circuits that use members of a collapsed group separately. Default runs without --allow-flat have the additional nested-AND restriction. No solver run or Lean build was performed during this review.

Reviewed UTC: 2026-11-25T15:03:25.852363+00:00
