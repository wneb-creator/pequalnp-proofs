# L-meta-2602 checked graph/circuit lower-bound inventory

The exact leased statement forbids a 63/64-gate ordered AND/OR fan-in-two circuit for the order-three incidence graph when both syntactic directional derivatives on edge (0,13) vanish.

## Strongest checked bounds

- L2237:1877: C4-free + IsAO2 + exact graph function + IsReadK 1 yields a vertex cover T with |E|+|T| <= size+1. This gives64 for the plane, but the requested derivatives explicitly indicate a repeated-read obstruction, so its read1 hypothesis is not available.
- L2235:1769: the same edge-plus-cover accounting for the subset of edges that have a read-once witness. This is valid without a global read1 assumption.
- L3706:1515: for D = edges with ReadTwiceAt at the output and a minimum cover K of G-D, |E|+|K| <= size+|D|+1. The repeated-read correction is on the wrong side to force strictness.
- L1491:2496 (also L4183): for a least circuit in TopForm, |E|+|tops-centreless|+2|centreless|+|junk|+|orN-lam| <= size+|Ustar|+1; cover(G-Ustar) <= |tops-centreless|. This is the strongest exact general accounting found, but requires control of missing-star edges and junk.
- L4803:1004 (helper main:981): exact plane computation + IsAO2 + no nested AND gives64 <= size. L1751/L2059/L5158 are related flat-circuit64 bounds for even weaker promise correctness.
- L3760:10036: least bipartite C4-free circuits never have exactly one junk AND. It does not eliminate two or more junk gates.

## Normalization and derivative interfaces

- L4181:1457: any exact Monotone2 graph circuit normalizes to a least AO2 circuit in TopForm of no larger size. No syntactic derivative preservation is asserted.
- L1501:1118: equal-size TopForm normalization preserving junk count.
- L3708:667: an edge is not ReadTwiceAt iff some AND in the OR-to-output frontier has its endpoints in opposite pure-OR input sets. Useful for identifying the precise missing read-once witnesses.
- L2067:473: if andPairs=0 then the syntactic derivative along any incident edge is true.
- L2069:874: for size<=64, positive andPairs, and every AND gate below the output function, at least one of the two syntactic derivatives is true. Thus the unresolved obstruction is dirty/internal AND gates, not a missing derivative identity.
- L2615:2385: a stronger clean-circuit incidence witness contradiction; its CleanHyp includes size<=64 and every AND below the output.
- L3652:820: under lift-fixed-point, live gates, and no implying operand, a doubleReread edge belongs to the union of maximal-core edge sets.
- L1961:8841: with size<64, nested AND and andPairs<=1, the promised circuit can be made strictly smaller. L3799:8 treats andPairs>=2 when every AND has at least two readers. Neither directly covers size64 or preserves derivative failure.

## Important false leads

- L3444, L3446, L2969 are checked REFUTATIONS of proposed maximal-core accounting inequalities. Their final theorem starts with negation; they cannot be used as positive charging lemmas.
- L1601/L1602 assume the desired clean-circuit edge-plus-cover lower bound as a hypothesis; they are transports, not unconditional lower bounds.
- L4219's63 bound assumes all terminal-AND inputs are raw inputs<26; its premises are inconsistent, so it provides no circuit bound here.
- R_meta_2602_2 and R_meta_2602_415 are reductions with unproved face/path hypotheses. The reduction capacity is already full; do not treat them as solved components.

## Best reusable route

A complete proof needs a new strict penalty/cleanup argument for the dirty ANDs forced by both derivatives vanishing. Existing clean-case bounds and derivative lemmas handle the remaining case. Any minimum-size normalization must either preserve the offending edge's syntactic derivative property or charge at least one deleted gate; semantic equality alone does not preserve it. A general unrestricted64 theorem was not found in the checked library census.

The small GraphSearch.lean component proves only the finite plane geometry and matching lower bound, independently of circuit normalization. Its Lean build status is recorded separately.
