# L-meta-2448 library route

## Least circuit existence

`lean/PEqualNP/Outside/L_meta_2666.lean` (143 lines) proves existence of a least monotone circuit for every graph edge function, without triangle/C4 assumptions. `L_meta_7069.lean` proves exactly h1 of reduction R_meta_2448_1.

Adapted proof in `results/orch/lemmas/StarLibrary.lean` (141 lines), with only PEqualNP.Defs imported, under namespace PEqualNP.Outside.L_meta_2448 and helper `least_exists`. Compilation passed: lake env lean, exit 0, only PEqualNP.Defs imported. DNF construction creates an OR-false seed and two gates per directed edge, then uses Nat.find to choose minimum size.

## Structural routes

- R_meta_2448_263 (477 lines) proves `pairDirt`: if one fan-in-two AND gate owns two disjoint edges of a C4-free graph, it fires on a non-edge pair among the four endpoints. Its final minimization argument minimizes the number of gates owning disjoint edges, provided two repair lemmas (singleton dirt and genuine pair dirt) decrease that count without increasing size.
- R_meta_2448_17 proves ownership around a five-cycle forces a true singleton, then uses a separate extension hypothesis to build star profile gate by gate.
- L_meta_1599 (235 lines) proves every graph edge is owned in any AND/OR-only circuit computing the edge function.
- L_meta_4181 (1474 lines) and L_meta_7860 (1153 lines) establish existence of least TopForm circuits. TopForm alone does not assert all junk AND gates have star ownership.

Only three HasStarProfile routes were found, all reductions; no direct accepted star-profile theorem is already available through PEqualNP.Defs. The substantive remaining task is size-preserving repair of an AND gate owning disjoint graph edges.

## Exact local lemmas for a normalization proof

- L_meta_1600 (402 lines): for a C4-free graph, an AND gate which is semantically below graphFun has empty or star ownership. This is stronger than the pair-dirt contrapositive and does not require triangle-freeness.
- L_meta_4846 (356 lines): C4-free + two vertex-disjoint owned graph edges implies the gate fires on some non-edge pair.
- L_meta_7406 (370 lines), L_meta_8547 (373 lines): triangle-free + C4-free strengthens the offending pair to one vertex from each owned edge.
- L_meta_8413 (487 lines): owning three consecutive edges forces a true singleton among their vertices or the closing pair.
- L_meta_1906 (946 lines): assuming every AND gate is semantically below graphFun, remove redundant/non-owning gates without increasing size, until every AND owns an edge. Its soundness hypothesis is substantive; it does not normalize arbitrary least circuits.

An ownership-name census found 14 accepted L_meta files using Owns. None proves the missing size-preserving repair of dirty ownership. The existence proof compiled successfully after Defs.olean infrastructure build completed.

## Follow-up: can disjoint ownership force an operand below the output?

This local route does not gain force from the new least_no_and_operand_below lemma. For ANY AND gate owning an edge uv, ownership descent (`owns_reach` in R_meta_2448_263 / the geometry adaptation) says each operand has an OR-only reachability path from u or v. Therefore each operand accepts at least one singleton input. Since graphFun G empty rejects every singleton, every operand already fails to imply the output, without minimality and without graph hypotheses.

Thus the checked normal form excludes a different pattern: an AND operand already containing a full edge computation. It imposes no additional restriction at the very gates whose ownership must be repaired.

Concrete irredundant local obstruction: on a matching ab + cd, the seven-gate circuit ((a OR c) AND (b OR d)) AND ((a OR d) AND (b OR c)) has two bad owning AND gates. Every AND operand fails to imply the graph output: first-layer operands have singleton witnesses and the final operands have nonedge-pair witnesses. The circuit is not globally minimum (three gates suffice), demonstrating that the necessary exchange can involve multiple gates rather than a bypass of one operand.

No counterexample to the proposed implication WITH full global minimality is established. Such an implication would prove that every minimum circuit has star profile, stronger than the posted existence statement. The finite-search agent reports no dirty minimum witness so far (P4 and C5 dirty-minimum synthesis UNSAT).

## Further primary-source search, 2026-11-25

The Amano–Maruoka technical report is listed by its primary institutional repository at https://ipsj.ixsq.nii.ac.jp/records/31828, with file IPSJ-AL04097006.pdf and publication date 2004-10-14. Both record and PDF returned HTTP429 to the read-only browser. The final Algorithmica article at https://doi.org/10.1007/s00453-006-0073-0 has an accessible abstract but inaccessible full text. Lenz–Wegener at https://www.sciencedirect.com/science/article/pii/0304397591901947 has an accessible abstract; its PDF returned HTTP403. The latter abstract studies the minimum AND count. Neither accessible abstract establishes the required total-size normalization. Any detailed high-girth claim attributed to these full papers remains UNVERIFIED because their bodies were not read.

The complete primary Katz paper https://arxiv.org/pdf/1206.6068 was read. It concerns a CNF representation of a bipartite edge relation, rather than exact evaluation of graphFun on arbitrary sets of vertices. Consequently its small graph-CNF upper bound is not a circuit counterexample to the current statement.

## A possible shared-OR accounting constraint

This is a direct mathematical observation, not a completed proof or literature claim. If a pure OR signal with variable support S is reused as the neighbor OR of a clean star centered outside S, then girth at least five forces any two distinct vertices in S to be nonadjacent and to have no common neighbor already in the core graph. Otherwise the new center creates a triangle or a four-cycle. Two such external supports also cannot intersect in two vertices.

For example, the P4 function ab OR ad OR cd has the dirty CNF (a OR c) AND (b OR d) AND (a OR d), using five gates, compared with four in a star circuit. Outsourcing the first two OR nodes to external stars superficially looks profitable. It is forbidden: a and c have common neighbor d, while b and d have common neighbor a. The new centers would create four-cycles. By contrast the matching gadget has four reusable nonedge-pair ORs; attaching forced clean stars to all four reaches the canonical cost but does not beat it.

This suggests charging shared OR savings through the no-common-neighbor condition. A complete invariant would still have to handle mixed OR signals containing earlier AND outputs and general fanout. No such invariant, full normalization proof, or counterexample was obtained by this route.
