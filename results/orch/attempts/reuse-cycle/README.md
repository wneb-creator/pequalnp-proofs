# Uncompiled cyclic-factor-reuse attempt

`ReuseCycle.lean` is an uncompiled attempt, excluded from the compiled-lemma census. The Lean run was interrupted with exit 130 after reaching approximately 4.94 GB RSS; the complete in-progress log is preserved. No Lean validation is claimed.

The construction uses ten vertices: five base vertices indexed cyclically and five pendant vertices. Edges join each base vertex to its pendant and join each base vertex to the vertex two positions ahead, giving a pentagon with five leaves. Five matching-two blocks are expressed as four-clause CNFs; adjacent blocks share an OR factor, producing a cycle of block reuse.

The candidate circuit has 34 gates. Python independently checked all 1,024 inputs and checked that every gate is pivotal on at least one graph edge. A separate 14-gate clean star circuit computes the same function. The exact data are in `reuse-cycle.json`. These finite checks demonstrate a nonminimum obstruction to geometry-only acyclicity; they do not refute L-meta-1772 and do not establish any below-budget obstruction.
