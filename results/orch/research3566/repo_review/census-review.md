# Independent graph census and synthesis review

Reviewer: pilot-178 subagent repo_review. Scope: research artifacts for L-meta-3566, not a Lean proof or certified circuit lower bound.

## Verdict

PASS for the representatives, counts within the explicitly stated census domains, and the counterexample thresholds. The scripts and logs must retain their domain qualifications. A timeout or UNSAT answer from the current restricted, exact-size SAT search is diagnostic only.

The independent verifier is `audit_census.py`; its complete stdout/stderr is `census-audit.log`, and its detailed result, matching witnesses, row masks, and source SHA256 hashes are in `census-audit.json`. It completed successfully in 19.412 seconds. It did not invoke a solver or Lean, import the original census scripts, or modify the original artifacts.

## Enumeration correctness and scope

* `census5x5.py` examines all C(20,7)=77,520 choices of seven off-diagonal edges added to the fixed diagonal perfect matching on a specified 5+5 bipartition. It accepts exactly 260 labeled graphs and finds two isomorphism classes. There is no separate minimum-degree filter. This directly establishes completeness for 5x5 graphs with twelve edges and a perfect matching, not an unstated unrestricted graph domain.
* `census6x6.py` enumerates six-by-six graphs with sixteen edges, a fixed diagonal perfect matching, and minimum degree at least two on both sides. Sorted left profiles are (4,3,3,2,2,2) and (3,3,3,3,2,2). There are zero and 48 accepted profile-ordered labelings respectively, giving one class.
* `census6x6m15.py` uses the same matching/minimum-degree restrictions at fifteen edges. Its profiles (5,2,2,2,2,2), (4,3,2,2,2,2), and (3,3,3,2,2,2) accept 5, 120, and 546 labelings respectively: 671 total and seven classes. This does not cover all six-by-six fifteen-edge graphs: adding a leaf on the smaller side of the 5x6 fourteen-edge representative gives a six-by-six fifteen-edge graph outside the minimum-degree-two domain.
* `bip5x6_14.json` is a checked representative, not itself a preserved enumeration script. It has fourteen distinct edges, no four-cycle, and a matching saturating the side of size five. Its two right neighborhoods of size three are {0,1,2} and {0,3,4}; the other four neighborhoods are {1,3}, {1,4}, {2,3}, {2,4}. No completeness claim is needed to use it as a synthesis target.

For the two 6x6 enumerations, the profile list was independently generated from all nondecreasing degree partitions with sum fifteen or sixteen, minimum degree two, and sum binomial(degree,2) at most fifteen. The latter bound follows because a C4-free graph has at most one common neighbor for each pair on the opposite side. The resulting profile sets equal the source lists. Fixing a perfect matching is harmless within the perfect-matching domain: relabel the matched right endpoints after sorting the left degrees. The column-degree and pair-count pruning in the source is necessary for the stated domain and does not discard a valid completion.

The canonical key minimizes the sorted row masks over all column permutations and over transposition. This handles independent permutations of both sides and interchange of the two equal-size sides. It does not identify two nonisomorphic graphs. All reported representatives are connected (independently checked), so no unaccounted component-wise bipartition swap affects their class count. Independently recomputed canonical keys match the JSON files.

Every reported cycle basis was also checked for simple cycles of length at least six, edge membership, GF(2) independence, and the correct rank m-n+components.

## Numeric representative checks

All rows below passed: unique correctly ranged bipartite edges, maximum common-neighbor count at most one, explicit maximum matching, cover size, exhaustive cover cardinality, canonical row masks, and listed degree data.

| Representative | n | m | tau | Positive + maximal-negative rows | Expected size m+tau-1 | Refuting size at most |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 5x5 m12 class0 | 10 | 12 | 5 | 12+17=29 | 16 | 15 |
| 5x5 m12 class1 | 10 | 12 | 5 | 12+14=26 | 16 | 15 |
| 6x6 m16 class0 | 12 | 16 | 6 | 16+23=39 | 21 | 20 |
| 6x6 m15 class0 | 12 | 15 | 6 | 15+21=36 | 20 | 19 |
| 6x6 m15 class1 | 12 | 15 | 6 | 15+33=48 | 20 | 19 |
| 6x6 m15 class2 | 12 | 15 | 6 | 15+24=39 | 20 | 19 |
| 6x6 m15 class3 | 12 | 15 | 6 | 15+23=38 | 20 | 19 |
| 6x6 m15 class4 | 12 | 15 | 6 | 15+23=38 | 20 | 19 |
| 6x6 m15 class5 | 12 | 15 | 6 | 15+24=39 | 20 | 19 |
| 6x6 m15 class6 | 12 | 15 | 6 | 15+26=41 | 20 | 19 |
| 5x6 m14 | 11 | 14 | 5 | 14+17=31 | 18 | 17 |

The minimum-cover certificate requires no unverified application of Konig's theorem here: a matching of size k forces every cover to have at least k vertices, and the smaller bipartition side itself is a cover of exactly k vertices. The verifier additionally enumerated all subsets and confirmed the same optimum.

A circuit with s <= m+tau-2 contradicts the full lower bound m+tau <= s+1. The checked `lower_bound_of_peeling` and `not_peeling_of_small_circuit` helpers translate such a circuit into a refutation of the globally quantified posted peeling statement. A circuit of size exactly m+tau-1 only matches the known construction and does not refute the statement. Every candidate must still be an AO2 circuit computing the exact graph function and must be kernel-checked before a formal result is claimed.

## SAT encoding and flags

The inspected `synth.py` chooses exactly K topologically ordered binary AND/OR gates, with one-hot operands and a final output at the last gate. Boolean truth-table clauses have the correct polarity. Positive rows are the m edge assignments; negative rows are all maximal independent sets. A monotone output that is correct on these rows is correct everywhere: any positive input contains an edge assignment, and every negative input extends to a maximal independent set. The code also exhaustively reevaluates all 2^n assignments before writing a SAT witness.

`irredundant` requires, for each gate, sampled rows witnessing both operand patterns (true,false) and (false,true). This has a valid least-circuit justification: if one pattern is absent, replace the gate with the appropriate operand. All subsequent sampled outputs remain unchanged; the smaller circuit remains monotone; boundary-row completeness restores correctness on every input. Internal wire functions need not be preserved away from the samples. This is a mathematical search-normalization argument, not a newly kernel-checked lemma in this job.

`two_dirty` selects at least two distinct AND gates true on some maximal negative row. For monotone signals, being true on any negative input is equivalent to being true on some maximal negative input. Existing recorded results rule out both zero dirty gates in a sub-bound circuit and exactly one dirty gate in a globally least bipartite NoFourCycle circuit. Thus the flag is motivated for a globally least counterexample. It is not automatically a completeness assertion at an arbitrary fixed K.

`topform` defines a clean AND exactly as an AND false on every maximal negative row, propagates clean-ancestor indicators, and forbids an AND from receiving a signal with a clean AND ancestor. This matches the intended top-form condition. Recorded normalizers support searching for a least counterexample in this form while preserving size and dirty-gate count. No new general normalizer is assumed proved by the current SAT run.

The base live-gate, essential-input, and operand-ordering constraints also express least-circuit normalizations. `solver_sat` changes solver heuristics only. The queued runs combine the flags at one exact K, rather than searching every size <=K; padding a smaller circuit may violate live/irredundancy constraints. Consequently even a completed UNSAT answer is not a proof that no smaller circuit exists, and a timeout says still less. SAT results remain useful because a fully checked witness is valid regardless of search restrictions.

No solver UNSAT certificate has been imported into Lean or presented as a lower-bound proof by this review.
