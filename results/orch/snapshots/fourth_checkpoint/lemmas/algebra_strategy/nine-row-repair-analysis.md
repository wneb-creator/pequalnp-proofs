# Nine-row repair and sharing analysis

The lifted43-gate approximation has four added point-line edges in its22-input numbering:

- (0,16): original point0 / line20.
- (2,9): original point2 / line13.
- (2,12): original point2 / line16.
- (2,18): original point2 / line22.

It computes a merged rectangle on points0,2 and lines9,10,12,16,18, a separate point2 product with20 OR21, and seven correct row stars. The existing saving comes from reusing line12 OR16 inside the merged union and row5. The added row7 could instead reuse9 OR16; old row6 could reuse16 OR18. Simultaneously exposing these overlapping pairs adds one OR to the merged-union construction for every extra saved OR in a row, so that direct rearrangement does not lower the total.

Finite weighted-cover checks considered all401 rectangles contained in this40-edge augmented graph. Minimum weighted rectangle cover corresponds to44 gates before OR sharing. A model allowing globally shared disjoint OR-pair atoms reached and proved optimum43 within that model. This is a computational result for that restricted construction class, not a Lean theorem or a lower bound for arbitrary circuits. The follow-up10-second model allowing subsets of the four unwanted edges found no incumbent and is inconclusive.

A direct one-rectangle augmentation scan on all nine rows considered6770 admissible cases with at most four added edges, using greedy common-OR extraction. Best remained43 gates and67 false maximal negatives. It produced24 distinct best functions, including eight whose merged pairs use newly added rows. The pool was delivered to circuit_search.

## New nonlinear seed families

For a merged point group S and any proper nonempty subset A, the guard OR(A) OR OR(N(S minus A)) preserves every original edge. Multiplying the merged rectangle by several such guards can leave genuine cubic error monomials, unlike the original bilinear approximations.

Direct singleton-owner guard generation tested19488 constructions in7.9 seconds; general partition extensions tested15442 in6.1 seconds. A curated159-seed bank contains39-43-gate circuits and includes32 three-guard topologies. Every seed retains all36 required edges, rejects singleton/pure-side inputs, and has a supplied cubic minimal-error witness checked against all point-line pairs. Best false-maximal-negative count is145, worse than67, so these are diversity seeds only. The39-gate variants leave four spare gates for later rewiring. No four-guard candidate fit43 in the tested construction orders.

No exact43-gate witness or strict semantic repair of the67-error approximation was found. All finite experiments terminated; no additional persistent search lane was launched.
