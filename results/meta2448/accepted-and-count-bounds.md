# Accepted AND-count results relevant to L-meta-2448

Investigated by proof_routes on2026-11-25. These are accepted repository theorems; their new specializations have not been compiled in the2448 target, and no normalization to a minimum star-profile circuit is claimed.

## General bound through cover rank five

`lean/PEqualNP/Outside/L_meta_217.lean:7350` proves: if t<=5, G has no four-cycle, every vertex cover of G has size at least t, C is Monotone2 and computes the exact graph edge function, and A contains every AND-gate index of C, then t<=A.card. It assumes neither triangle-freeness, minimality nor star ownership. Consequently it gives AND>=tau for every graph with tau<=5, and AND>=5 for any C4-free graph with larger cover number.

This is a7353-line finite-classification proof, not a general algebraic normalization. Lines56–140 reduce to a vertex-critical induced graph on at most2t vertices. Lines1422–1454 (`collapse_and_count`) turn the original circuit into an `AndCountCircuit` with no more AND gates, preserving the graph function. OR networks are collapsed into arbitrarily large disjunctive sides. Lines7318–7344 assemble a361-graph catalogue and kernel-checked finite certificates; the last theorem combines those certificates with the graph reduction.

The collapse preserves neither the number of OR gates nor a bound on the number of OR gates needed to recompile the abstract sides. It produces no HasStarProfile statement and no minimum-total-size star circuit. It therefore cannot be used to finish2448 merely by observing that a star construction has the same AND count.

## Petersen-specific rank six

`lean/PEqualNP/Outside/L_meta_635.lean` uses exactly the Petersen labeling in the current synthesis input: outer cycle01,12,23,34,40; spokes05,16,27,38,49; inner star57,68,79,85,96. Its second conclusion excludes every well-formed `AndCountCircuit` of size<=5 satisfying the maximal-independent-set boundary promise. Exact graph computation implies that promise, so the generic collapse above yields at least6 ANDs for root-model exact Petersen circuits. This is stronger than applying217 with t=5.

`L_meta_634.lean` analogously gives at least7 AND-count gates for the14-vertex Fano incidence graph. `L_meta_958.lean` and `L_meta_962.lean` supply the cover-rank4 and5 conclusions even for the weaker maximal-independent-set boundary promise. `L_meta_1006.lean` refutes an unbounded version of that WEAKER promise claim; its statement is not an exact-graph-function refutation, so it does not settle the general exact AND>=tau question.

## Easier exponential bound

`L_meta_216.lean` proves that k ANDs permit at most2^k maximal false inputs. For graph functions those inputs are exactly maximal independent sets. The independent finite counts in `and-count-mis-diagnostic.json` therefore give3 ANDs for C5/C6 and4 for the8-vertex adjacent-Petersen-deletion core. C7 has7 maximal independent sets, so216 alone gives only3;217 strengthens that to the correct cover bound4.

For proper backward binary circuits, swapping AND and OR computes the Boolean dual x |-> not F(not x). Minimal true inputs of F become maximal false inputs of its dual. Thus216 also gives |E|<=2^(OR count), and the10-edge core needs at least4 ORs. This exponential OR bound is much weaker than the missing9-OR bound for that core.

## Scope of the bounded search

The repository census examined47 files mentioning named vertex-cover notions,345 files mentioning SimpleGraph, the AND-count declarations within those, and all26 accepted files containing AndCountCircuit. No unconditional exact AND>=tau theorem for arbitrary cover number was found. No general biclique-cover equality is asserted.
