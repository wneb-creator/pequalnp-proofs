# AND-root and unique-input architecture assessment

Author: lower_bound. Date: 2026-11-25. Scope: bounded mathematical analysis and short exact probes, with no new solver run or Lean build. The 26-gate gap remains unresolved.

## Linear root factors

Write the edge function as `G = OR(S) AND B`, with both factors monotone. Every edge must meet S, so S is a vertex cover. If its independent complement I is not maximal, every maximal false input intersects S. Then B must reject all maximal false inputs and already equals G; the linear factor is redundant. A nonredundant linear factor therefore corresponds to a minimal vertex cover and discharges exactly one maximal false input, namely I.

The 37 maximal false inputs have part-size shapes `(7,0)` and `(0,7)` once each, `(4,1)` and `(1,4)` seven times each, and `(2,2)` 21 times. Their complementary covers have sizes 7, 9, and 10. An explicit minimum-size OR tree costs 6, 8, or 9 gates; after the final AND, a 26-gate construction leaves respectively 19, 17, or 16 additional partner gates. All OR-tree intermediates may be shared with the partner. This is a concrete fixed-factor architecture, not a claim that every representation of a linear factor can be replaced by that tree without affecting sharing.

The largest permitted partner is `Bmax = G OR D_I`, where D_I holds on subsets of I that meet the neighborhood of every vertex outside I. Its minimal added terms are:

- For a whole bipartition I, the seven three-element neighborhoods on that side.
- For I of shape `(1,4)` or `(4,1)`, the isolated-side vertex together with any three of the four opposite-side vertices: four degree-four terms.
- For I of shape `(2,2)`, the single degree-four term containing all four vertices.

The finite probe verifies all 37 identities on all 16384 assignments, totaling 606208 checks. A factor in an actual circuit may lie strictly between G and Bmax; requiring the exact maximal partner is an optional construction search, not a complete normalization. This analysis does not rule out a single linear root factor. Two linear factors alone cannot compute Heawood: their singleton supports must be disjoint and their cross product would have to be the graph, contradicting its degree-three C4-free structure.

## Concrete next cut searches

The simplest proposal fixes a six-gate OR of all left inputs and asks for a 19-new-gate partner using its six intermediate wires as correlated cut inputs. The partner must accept all 21 positive boundary rows and reject the 36 maximal false rows other than the all-right input. That is sufficient for the final AND to be exact.

A richer factor is `H_r = OR(right vertices other than r) OR (r AND OR(N(r)))`. It costs nine gates and rejects exactly two maximal false rows. A 16-new-gate partner can reuse all nine factor wires. More generally, replacing k of the seven linear right inputs by their full target stars costs `6+3k` gates; for k<=3 it rejects `1+k+choose(k,2)` maximal false inputs, leaving `19-3k` new partner gates. These are optional fixed-factor families, not an exhaustive enumeration of all partitions of the 37 maximal false inputs.

For arbitrary AND-root fanins, let A and B be their accepted singleton supports. The target's singleton rejection makes A and B disjoint; target pair rejection makes every cross pair an edge. C4-freeness implies that, if both are nonempty, one is a singleton and the other is a subset of its three neighbors. The exhaustive nonempty support-size counts are 42 of `(1,1)`, 42 each of `(1,2)` and `(2,1)`, and 14 each of `(1,3)` and `(3,1)`. Otherwise at least one fanin has empty singleton support. This is a complete semantic root split, with no restriction on higher-degree intermediates.

## Stronger unique-input observations

The root's raw-occurrence argument led to the separately reviewed unique-input CNF. For unique input 0, the partner W of its sole consumer must transmit the target's dependence on 0. Therefore W is true for an AND consumer and false for an OR consumer on the 25 maximal false boundary rows omitting 0 and the three positive edge rows containing 0. These 28 existing rows require no extra row variables. Exact CNF review is in `unique-input-review.md`.

For an OR consumer, a stronger semantic bound is available. Let `F0` be the edge function after deleting vertex 0. Every independent input accepted by W must block all three neighbors 7,8,10 of 0; otherwise adding an unblocked neighbor gives an influence assignment, contradicting W=true. Each other left vertex blocks at most one of those neighbors, and right vertices block none. Thus W rejects all singletons and all nonedge pairs. More precisely,

`W <= F0 OR ((x1 OR x3) AND (x2 OR x6) AND (x4 OR x5))`.

The eight minimal independent exceptions choose one vertex from each displayed pair. This constrains W's output only; it does not imply that its internal AND gates are clean. For an AND consumer, W must accept each of the three neighbor singletons, so its singleton support contains `{7,8,10}`.

## Reproduction and status

- Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/and_root_probe.py`
- Complete successful log: `/tmp/oec/pequalnp-pilot-70/lower-bound/and-root-probe-check-2.log`
- Initial syntax-only failure log retained: `and-root-probe.log`.

The successful probe exited 0 in under one second. It enumerates all maximal false inputs, all allowed linear-factor additions, every singleton-support root pair, and the eight unique-OR partner exceptions. No circuit-size optimum, unrestricted normalization, or complete UNSAT result is asserted.
