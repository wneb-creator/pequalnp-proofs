# Constructive analysis for L-meta-1342

The explicit graph has THREE triangles: {1,4,8}, {3,6,7}, {5,8,9}. The overlap between the first and third is vertex8.

## Exact near witnesses

`unit-prefix22.json` computes the target on all2048inputs with22gates,7ANDs, and exactly one junk AND at index2. The first3gates are OR(8,0), OR(9,4), AND of these. The remaining19gates are a continuation using the original inputs and these three prefix wires.

The identity is ((a OR b) AND (c OR d)) AND (a OR c) = (a AND c) OR (a AND d) OR (b AND c). For a=8,b=0,c=9,d=4, this covers edges89,48,09. The filter OR(8,9) is shared with the star5 AND (2 OR8 OR9), making this dirty replacement cost-neutral versus a minimum-cover22gate circuit. This is an actual full-function construction, not a pair-row approximation.

`neutral-units22.json` gives five such22gate circuits, found by enumerating triangle/P4 patterns and residual five-covers. The five distinct units are:

* (1 OR5) AND (2 OR8)
* (2 OR8) AND (4 OR5)
* (0 OR5) AND (2 OR9)
* (0 OR8) AND (1 OR9)
* (0 OR8) AND (4 OR9)

All five use triangle{5,8,9}, have one junk AND and19gate continuation, and pass full2048row audit. None establishes an18gate continuation or the posted21gate conclusion.

`two-junk24.json` is a full-function24gate seed with exactly two junk ANDs, from majority CNFs for triangles{1,4,8} and{3,6,7} plus residual stars. It may help search but is farther from the target.

## Rejected gadget family

`triangle_gadgets.py` exhausts44 triangle-plus-selected-pendant three-clause CNFs;35 are sound below the target,9 accept false independent triples. In particular, using all three pendant classes around triangle{5,8,9} accepts independent{0,1,2}, although pair rows look correct. This proposal was retracted immediately after sibling review.

Joining each sound member of that family with an optimal residual star cover, without cross-gadget sharing, yields minimum23gates. The neutral22construction above succeeds by sharing the filter OR with an existing third-center star; ordinary isolated substitution cannot improve22.

## Lean status

`Unit22.lean` defines the exact22gate witness and has easy shape/size proofs. The final direct finite-function `decide +kernel` attempt exceeded2GiB, as recorded in unit22.log; the complete file did NOT compile. Sibling is independently replacing that final proof using Boolean-expression simplification in a separate file. Do not present this scratch file as checked until that replacement succeeds.

## Stronger exact two-junk22 witness

`two-junk22.json` supersedes the24gate seed: it computes the complete target with22gates,7ANDs, and exactly two junk ANDs at indices2 and7. Full2048input audit has no mismatches. The first dirty unit stays (8 OR0) AND (9 OR4). The second is Q=(7 OR10) AND (6 OR9), wrapped as (6 OR7) AND (3 ORQ). This6gate block computes exactly edges36,37,67,6-10,7-9 and ties the cost of the old two-star block. The complete circuit still has a19gate continuation after its first3gate unit.

The sound generic identity is
(a ORc) AND (e OR ((a ORb) AND (c ORd)))
= (a ANDe) OR (c ANDe) OR (a ANDc) OR (a ANDd) OR (b ANDc).
This covers a triangle plus pendant groups at two vertices at the exact star cost. Unlike the rejected three-clause construction, putting the third triangle vertex e outside the dirty AND introduces no independent three-leaf minterm.

Sibling has now Lean-checked the earlier one-junk prefix22 witness in sibling/Unit22Checked.lean, including its exact19gate tail under augmented inputs; root/reviewer have frozen hash/log. Sibling is adapting the same proof to two-junk22 in a separate file. The exact junk count remains externally audited unless explicitly included in that later proof.
