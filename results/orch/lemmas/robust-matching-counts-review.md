# Independent review of RobustMatchingCounts

2026-11-25 UTC. Reviewer: constructive. Read-only review; no compilation, desk call, or git action.

Verdict: PASS for preservation as a checked partial. Reviewed all 100 lines of `/tmp/oec/pequalnp-pilot-70/lower-bound/RobustMatchingCounts.lean` and the complete empty `robust-matching-counts-lean.log`. The author reports compilation exit zero; this reviewer did not rerun Lean.

The three line permutations coincide with the independently enumerated matchings for the exact assignment edge list. Their inverse index arrays correctly assign the same matching index to each point and its matched line. Kernel decision proves the finite identities, edge membership, ordered-pair injection, and unordered `Sym2` edge injection.

`surviving_matching` is the correct three-versus-two pigeonhole argument on matching labels. `cover_seven_after_two` maps selected cover endpoints onto all seven matching indices, so it requires no unjustified injectivity of the cover map. The complement of at least 19 retained indexed edges has at most two elements. Finally, unordered-edge injection ensures that the retained indexed edges contribute their full cardinality to `J.edgeFinset`; no reversed-edge double counting occurs.

The final bound `26 <= J.edgeFinset.card + T.card` correctly combines at least 19 distinct present edges with cover size at least seven. J need not be a subgraph of Heawood for this implication, and the theorem does not silently assume that it is.

Only the permitted import and helper namespace are used. No forbidden `_root_` text, string literals, attributes, options, `sorry`, new axioms, `native_decide`, or `unsafe` commands were found. This remains a finite graph-counting helper, not a proof of the posted existential statement.
