# Point-private literals: proved mathematical branch and obstruction

This note gives a mathematical argument, not a completed Lean theorem. The general global lower bound of thirteen AND gates remains unproved.

## Circuit hypotheses and their sources

Let C be a free-OR AND-count circuit for the full incidence edge function of the projective plane of order three, with k ≤ 12 AND gates. Normalize by L_meta_563: every gate rejects singleton inputs and its two bare-variable sets are disjoint. This normalization applies to arbitrary circuits, including dirty intermediate gates, and preserves the entire function.

For each point p, let W_p be its set of signed bare occurrences (gate coordinate, left/right sign). Let U_p be the unsigned coordinate support. Normalization gives |W_p| = |U_p|. A signed literal is point-private if it occurs in W_p and in no other point word; occurrences in line words do not affect this definition.

The following necessary properties are used:

1. |U_p| ≤ 4 for every point. There are 197 distinct maximal false inputs containing p. The false-row code argument gives 197 ≤ 2^(k−|U_p|), hence |U_p| ≤ 4 at k ≤ 12.
2. |U_p ∪ U_q| ≤ 6 for distinct points. There are 52 maximal false inputs containing both. The same argument for the common set {p,q} gives 52 ≤ 2^(k−|U_p∪U_q|).
3. Every closed point set A admits a partial signed assignment which avoids all W_p for p∈A and hits all W_p for p∉A. Here “avoids” means no chosen coordinate-sign occurs in the word, and “hits” means at least one does. This is the direct generalization of the checked `mis_cover` proof in L_meta_910, lines473–553. Its premises are false output on a maximal false row, true output after inserting any omitted vertex, and absence of bare output variables. Full function correctness supplies these premises. The partial assignment selects a false side of each gate when one exists, leaving a gate unset when both sides are true.

The generic information bound in FreeRows.lean and the704-row data and197/52/70 counts in FalseRows.lean have now compiled with exit0. Their exact snapshots and complete logs were independently reviewed and pushed in19d9b3d7. The finite data were also independently enumerated by root. The no-private structural argument below remains a mathematical argument, not a Lean theorem.

For any point set T, define cl(T) to be the point part of its canonical maximal false extension: a point p lies in cl(T) iff every line through p meets T. For p∉T, each q∈T lies on exactly one of the four lines through p. Consequently p∉cl(T) whenever |T|≤3; if |T|=4, p∈cl(T) iff the four selected points lie on four distinct lines through p.

## Assume that no point word has a point-private literal

Every literal in W_p is then shared by some other point. If |W_p|≤3, choose one other sharing point per literal. This gives a set T of at most three other points whose words cover W_p. Since p∉cl(T), a partial assignment separating cl(T) must avoid every word in T but hit W_p, impossible. Hence every W_p has exactly four literals.

Fix p and choose one other sharing point q_j for each of its four literals. The same covering argument forces p∈cl({q_j}). Thus the q_j are distinct and occupy the four distinct lines through p. Keeping three representatives fixed and varying the representative of the fourth literal shows that every other point sharing that literal lies on its one assigned line through p.

Therefore each nonempty signed-literal sharing block B is contained in a unique geometric line (it has at least two points), and the four literals at each point are assigned to its four distinct incident lines. On each geometric line, the blocks partition its four points into parts of size at least two. Hence each of the thirteen lines is either:

- one block of size four; or
- two blocks of size two.

Let s be the number of split lines. There are 13−s four-blocks and 2s two-blocks. Distinct blocks on one line are disjoint. A pair of distinct points shares at most one same-sign literal, since it has only one common line.

## Count unsigned and opposite-sign intersections

Every point word has unsigned support size four. Property2 implies that each pair of points has unsigned support intersection at least two. Summed over the78 point pairs, total unsigned intersections are at least156.

The same-sign intersections count is exactly

    6(13−s) + 2s = 78−4s.

The first term counts the six pairs in each four-block; a split line contributes one pair in each of its two two-blocks. Thus total opposite-sign intersections are at least

    156 − (78−4s) = 78+4s.

At any coordinate the positive and negative point blocks are disjoint, because an individual word cannot contain both signs. Two four-blocks cannot occupy opposite signs of one coordinate: every two geometric lines meet, so their full point sets are not disjoint. A coordinate with two nonempty signs must therefore pair a four-block with a two-block, or two two-blocks.

Let f be the number of four/two coordinates and t the number of two/two coordinates. Then

    f + s ≤ 13,
    f + 2t ≤ 2s,
    78 + 4s ≤ 8f + 4t.

The first two inequalities count available blocks; the last counts opposite-sign point pairs. From the latter two, 78≤6f, hence f≥13. The first inequality forces s=0. The second then forces f=0, contradiction.

Thus at least one point word has a point-private signed literal. The dual argument gives a line-private literal among the line words. This does not yet imply thirteen AND coordinates: a private signed literal can share its coordinate with an opposite-sign block.

## Why the private case cannot be closed using point information alone

There is a concrete family of thirteen point words on twelve coordinates satisfying every canonical point-row separation and every point-subset information bound.

Start with five words on coordinates a,b,c,d:

    W1 = {c−,d+}
    W0 = {a+,b+,c+,d+}
    W4 = {a+,b−}
    W6 = {b+,d−}
    W2 = {a−,c+}.

The subscripts are the plane point labels. The four short-word points1,4,6,2 occupy the four distinct lines through the central point0. Give each of the other eight points its own fresh positive singleton literal.

An exhaustive check of all81 partial assignments on a,b,c,d shows that the sole inseparable selected subset of the five gadget words is all four short words with the central word omitted. No closed point set has this intersection pattern, since the four partners meet all four lines through0. The eight singleton coordinates can independently avoid or hit the remaining words. Thus every one of the704 canonical point-row projections is separated.

The unsigned pair unions are all at most six. A separate exhaustive check of all8192 point subsets S verified

    number of maximal false rows containing S
      ≤ 2^(12 − |union of U_p over p∈S|).

Full witnesses and the checks are in `full-point-side-countermodel.json`. This is a countermodel to the sufficiency of point-side necessary conditions, not an AND-circuit construction or a refutation of L-meta-2602. Any completion of the global bound must use cross-side line-word geometry or additional circuit structure.
