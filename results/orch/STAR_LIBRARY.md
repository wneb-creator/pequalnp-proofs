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
