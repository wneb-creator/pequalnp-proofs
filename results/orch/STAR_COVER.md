# Star-profile upper construction and conditional numerical route

Compiled with pinned Lean4.36.0 and only PEqualNP.Defs imported.

- Frozen initial checkpoint: lemmas/StarCoverCheckpoint.lean, 412 lines, successful star-cover-003.stdout/.stderr.
- Frozen final helper package: lemmas/StarCover.lean, 441 lines, successful star-cover-004.stdout/.stderr.

Namespace: PEqualNP.Outside.L_meta_2448.CoverConstruction.

## Checked results

`star_upper`: For ANY finite graph G and ANY vertex cover S, constructs a monotone fan-in-two circuit D computing graphFun G empty, with HasStarProfile and D.size at most |E(G)| + |S| - 1 (natural truncated subtraction). No triangle/C4 assumptions are required for this upper bound.

The construction adapts accepted L_meta_5355. It assigns each edge to a cover endpoint, creates one star gadget per nonempty owner, and ORs their outputs. The existing construction state already records that each AND gate forces its center input true. This implies star ownership directly on pair inputs, with no appeal to semantic cleanliness or girth.

`least_star_of_cover_lower`: If every computing monotone circuit has size at least |E(G)| + |S| - 1 for a chosen vertex cover S, the constructed star circuit is minimum. Its conclusion is exactly the per-graph existential demanded by the posted gap.

`min_cover_exists`: Every finite graph has a minimum vertex cover, by minimizing its cardinality with Nat.find.

`posted_of_cover_lower`: Its conclusion is copied verbatim from results/orch/statement_2448.txt. Its single hypothesis is a numerical lower bound: on triangle/C4-free graphs, every monotone circuit computing the edge function has size at least |E(G)| + |S| - 1 whenever S is a minimum vertex cover.

## Remaining task

The package is conditional, not a proof of L-meta-2448. It establishes that a numerical gate-count route suffices. The missing theorem is the sum lower bound |E| + minimum-cover-cardinality - 1. A suitable pair of separate lower bounds would supply it, but the tempting unrestricted OR-count bound |E|−1 is now refuted by the checked PrivateSupportLimitation example. The total bound would require a tradeoff argument; the general AND-count bound is also unproved.
