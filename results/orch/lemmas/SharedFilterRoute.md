# Shared-filter route: checked pieces and remaining bridge

The unrestricted L-meta-1477 lower bound is not proved by these files.

## Checked pieces

- `MultiOutputFrontier.lean`: a shared binary-DAG frontier bound for arbitrary finite label sets. Small label sets are free stops; genuine two-child branching nodes are paid once across all outputs.
- `MultiFilterActive.lean`: active labels retain their owning filter root. A shared node therefore inherits that owner's full clean-mask premise. Lambda nodes have at most one active label for uncredited owner products.
- `MultiFilterCount.lean`: one charge set outside Lambda and disjoint from mixing pays the union of active centers plus the number of filter roots.
- `MultiFilterStops.lean`: arbitrary additional stops with at most one active label can be excluded from that charge set.
- `MultiFilterBudget.lean`: complete mask/ordinary/multiple-filter budget, conditional on at most one active label at every live mask gate. This condition is not proved in general.
- `LabeledFrontier.lean`: the actual circuit adapter generalized to arbitrary label types, used by the singleton-pivot route.
- `SharedMaskCollision.lean` (root): if a mask node with cleaner q contains distinct clean-mask inputs c,d for an owner product A*B, with c an internal cleaner and an opposite internal cleaner b0, every bad cross pair has B-endpoint q. Thus q belongs to B and c-q is a shared mask edge.
- `ActualMaskCollision.lean`: this finite fact gives a shared edge and actual connectivity between enumerated mask roots. The owning filter remains explicit.
- `SharedMaskCollisionTwo.lean`: the same collision forces B.card <= 2 when A.card >= 2.
- `SharedMaskCoverExchange.lean`: all mask edges of the owner product are covered by {b0,q}; replacing c by q is valid when b0 and q are retained. Simultaneous exchanges are NOT justified.
- `SharedFilterEdgeCover.lean`: the finite global accounting lemma described next.

## Finite global accounting

Let P <= H be finite simple graphs, let P cover every vertex of S, and let R be a subset of S. Suppose each c in R minus Q has an H-neighbor q in Q distinct from some P-neighbor b. Then

    |S| + |R| <= |E(H)| + |E(P)| + |Q|.

Proof: active vertices outside Q with P-degree at most one choose distinct edges in H minus P. A chosen edge is outside P because its endpoint q differs from the existing P-neighbor; the choices are injective because exactly the active endpoint is outside Q. The remaining active vertices have P-degree at least two. Since every vertex of S has positive P-degree, the degree sum bounds their number by 2|E(P)| - |S|. Adding the two bounds gives the result. This lemma requires no C4 or bipartition assumption.

## Proposed circuit/component bridge (NOT proved)

A distinct cleaner input can have several disjoint OR outputs, so S should consist of components of the separate per-cleaner mask networks, not just distinct cleaner inputs. Roots of the same cleaner whose support networks meet belong to one component. An internal mask edge connects the component at each endpoint; call this component graph H. The two internal cleaners of each product give a product edge in P, so P should cover S and have at most t edges.

Before ordinary-owned edges are removed, separate per-cleaner Euler counting should give

    maskEdges + |E(H)| <= maskOR + |S|.

Cut the filter OR DAGs at encountered live mask components. Label each such cut by its component; direct active input leaves may use their owner component. A shared frontier argument should pay the distinct cut-component set Q using the remaining OR gates plus the number r of filter outputs. The checked collision theorem should give an H-neighbor in Q for each remaining owner label, distinct from its own product mate. Combining this with the checked finite edge-cover lemma would cancel |S| and |E(H)|.

Still missing: the actual per-cleaner component construction, the exact cut-label recursion/provenance, and the treatment of ordinary-owned spokes and credited boundary products. In particular, product-center edges can be owned, so one cannot simply assume P remains a subgraph of the residual H. Neither the conditional live-mask stop premise nor simultaneous group-merger refunds may be dropped without this bridge.
