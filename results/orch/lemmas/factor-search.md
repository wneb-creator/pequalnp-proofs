# Two-supergraph factor synthesis

2026-11-25 UTC. Constructive prototype requested by root. Only short, bounded searches were run; no desk, Lean build, or git action.

## Exact factor construction

Write the target bipartite graph as G. Among its 37 maximal independent sets, two are the whole bipartition sides. The remaining 35 consist of seven 1-by-4 rectangles, seven 4-by-1 rectangles, and 21 2-by-2 rectangles. Each contains four nonedges. Each of the 28 bipartite nonedges lies in exactly five mixed maximal independent sets.

Partition the 35 mixed false rows between two groups, with both pure-side false rows assigned to both groups. Let H and K be the largest bipartite graphs containing no edge internal to any false row assigned to their respective groups. They both contain G. Every maximal false row is rejected by at least one factor, while every target edge is accepted by both. Consequently `F_H AND F_K = F_G` on all inputs, not merely on the boundary.

An equivalent characterization uses added nonedges X and Y: every e=(a,b) in X and f=(c,d) in Y must satisfy `G(a,d) OR G(c,b)`. This condition is necessary and sufficient. If both factors accept using added edges, the union of their endpoints must already contain a target edge. Conversely a pair violating the condition produces a false positive on those endpoints. Such compatible e and f cannot share a left or right endpoint.

The resulting compatibility graph has 28 vertices, one per nonedge, and every vertex has exactly 18 neighbors. These counts and the 35-row classification were checked independently by direct Python enumeration.

## Complete enumeration of maximal compatible pairs

Every compatible X,Y pair has disjoint left supports and disjoint right supports. Choose a partition of the seven left vertices and a partition of the seven right vertices. X lies inside one product of parts and Y inside the opposite product. Across all 128^2 support cuts, the smaller allowed nonedge side has at most nine elements. Summing 2^m over all cuts gives only 664,598 subset cases before symmetry reduction.

The prototype enumerates subsets of the smaller side, intersects their compatibility neighborhoods, and closes both sides under common-neighbor operations. It deduplicates unordered pairs. Complementary support cuts are equivalent, leaving 8,192 cuts and 324,107 nonempty subset visits. Every globally maximal compatible pair appears: choose the cut from its actual supports and enumerate its smaller side.

Result: 5,033 maximal unordered pairs, in 3.194 seconds. Every generated pair was checked for mutual neighborhood closure. A separate validation recomputed all 37 maximal false rows and confirmed that every one of the 5,033 factor pairs rejects each such row in at least one factor, and accepts every target edge in both factors.

The 168 bipartition-preserving Heawood automorphisms were enumerated from permutations of the seven left vertices preserving the seven column triples. Quotienting the 5,033 pairs produced 45 orbits in 0.255 seconds. Orbit sizes sum to exactly 5,033. Part-swapping dualities were not needed and were not used.

This enumeration is exhaustive only for maximal compatible factor pairs. It is not an enumeration of all circuits, and maximal completion is not known to preserve minimum circuit size.

## Joint synthesis score

For each pair H,K, candidate terms are maximal bicliques of either factor, all row and column stars, and target-star subrectangles which can be shared by both factors. Weighted greedy covers choose terms for both factors together. Four row/column cover combinations provide additional baselines.

OR subsets on the left and right are built jointly using repeated-pair extraction, so intermediate ORs are shared. Identical AND terms are shared. If C is the disjunction of terms common to the two covers, the output is synthesized as `C OR (A AND B)`, using the Boolean absorption identity. This is cheaper than separately constructing `C OR A` and `C OR B` before the final AND.

The implementation also merges intermediate wires having identical values on all 58 boundary assignments. This preserves the final boundary behavior; because the resulting circuit is monotone, a correct target boundary implies correctness on every assignment. Retained best circuits additionally receive a separate full 16,384-input truth-table check.

The actual formal degree-one and degree-two components are propagated after gate construction. Candidates with at most 18 target edges in their degree-two shadow are tracked separately, preventing the ordinary 27-star circuit from suppressing genuine nested-factor candidates.

## Initial results

- Initial five-second partition smoke test: 874 partitions, best 27 gates. It exposed an excessive greedy preference for common target stars; the scoring was adjusted accordingly.
- Complete first pass over all 45 factor-pair orbit representatives: 2.090 seconds. Best overall 27 gates. Best candidate with at least three missing degree-two edge monomials: 37 gates, with 18 shadow edges, from factors with 25 and 33 edges. Both retained candidates have zero full-truth-table errors.
- These results do not prove optimality even within the two-factor family. Rectangle cover choice, OR sharing, absorption, and deeper Boolean identities are only heuristically optimized.

## Prototype files

All code, generated candidates, and complete logs are under `/tmp/oec/pequalnp-pilot-70/constructive/`:

- `factor_partition.py`: factor construction, joint covers, shared circuit construction, boundary and full-table checking.
- `factor_compatibility.py`, `compatible-pairs.json`, `compatible-pairs.log`: complete maximal-pair enumeration.
- `factor_orbits.py`, `factor-orbits.json`, `factor-orbits.log`: the 45 representatives and group quotient checks.
- `factor_score.py`, `factor-score-smoke.json`, `factor-score-smoke.log`: first complete scoring pass and retained circuits.
- `factor_milp.py`: time-bounded mixed-integer selection of joint rectangle covers, with at most 18 common target edges. Its objective is a gate-cost proxy; it is not a circuit lower-bound certificate.

Root authorized one scoring slot of at most two minutes after renewing the lease at 06:16:05 UTC. The mixed-integer cover-selection pass finished after 90.169 seconds, evaluating 109 orbit/objective-weight combinations. It improved the best genuine dirty-factor circuit to 36 gates, with 14 degree-two shadow edges, on orbit 29. The retained circuit has zero errors on the full 16,384-input truth table. Complete stdout/stderr is in `factor-milp-run1.log` and results in `factor-milp-run1.json`.

The mixed-integer objective charges for selected rectangles and required OR subsets, with three different sharing estimates. It enforces at most 18 target edges covered by common rectangles. The final gate count is measured on the actual shared circuit after boundary-signature merging and unused-gate removal. Even an optimal solution of this proxy would not establish optimal circuit size.

This phase is now stopped and its CPU slot is free. The 36-gate result is too far from 26 to justify claiming the current heuristic is promising. The 45 representative pairs may still be useful for focused SAT constraints on intermediate factor values or a stronger exact shared-circuit synthesis routine. No nonexistence conclusion follows.
