# L-meta-4675: semantic normalization and source checks

Read on 2026-11-25, beginning about 17:10 UTC. The root agent held the lease and handled all desk calls. Work stopped immediately when the root reported a desk HTTP 405 and invoked the task's error-stop rule. No live lease is assumed after that notice. This note records research only; no proof or refutation of the posted statement has been obtained here.

The statement in `/tmp/oec/pequalnp-pilot-99/gap4675/statement.txt` removes the extra semantic star witnesses from L-meta-4970. It asks for the full `|E| + |S| <= C.size + 1` bound for every exact AO2 computation of a C4-free bipartite edge function with syntactic `TwoColour.tCount = 0`.

## The semantic obstruction

`lean/PEqualNP/Defs/TwoColour.lean:14` explicitly stops OR reach at every AND gate. Consequently T0 does not imply that a gate's Boolean function is monochromatic. The independent reviewer's exact live example is preserved at `/tmp/oec/pequalnp-pilot-99/gap4675/status_review/t0-mixed-or-obstruction.json`: shield the two raw inputs by duplicate-input ANDs, take their OR, and intersect it with the edge product. The result computes the single edge with T0 even though its internal OR is semantically mixed.

The first-dirty-AND route therefore needs a cost-aware transformation. For a private rectangle `(OR A) AND (OR B)`, a one-color selector can expose a star using an existing side OR. Several rectangles with a shared selector also have elementary distributive rewrites, already checked in the earlier RectangleLayer component. This does not yet handle OR-sharing between dirty rectangles and later selectors hidden behind AND gates. No general purity, absorption, or no-cost homogenization claim is used.

`lean/PEqualNP/Outside/L_meta_8933.lean:1469` gives the full numerical conclusion under absence of a particular dirty AND accepting two repeated-read edges. T0 alone cannot imply its hypothesis: appending a dead all-points/all-lines rectangle preserves T0 and the earlier output while creating such a dirty gate. The library agent owns investigation of a minimality/charging repair.

A proposed first-dirty C8 SAT probe was cancelled before execution: existence of a dirty optimal representative would not refute existence of an equally small clean representative. The counterexample agent instead owns the useful variable-graph search, with complete truth-table checks.

## Primary-source checks

These sources were opened through the read-only web tool on 2026-11-25.

* Jukna, [Disproving the Single Level Conjecture](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf), 2006, sections 3.1 and 8: graph representation only constrains selected pairs, whereas the quadratic edge function must be correct on the whole Boolean cube. The separating circuit constructions use saturated extensions adding cliques within both sides. They therefore do not directly produce C4-free bipartite counterexamples. Problem 8.2 asks for explicit superlinear monotone circuit lower bounds for quadratic functions. Its current 2026 status is **UNVERIFIED**; the historical statement alone is not a current-status claim.
* Jukna, [Explicit dense K2,2-free graphs with small CNF representation](https://web.vu.lt/mif/s.jukna/boolean/CNF.html), January 2024: the small CNFs describe the bipartite graph on one-left/one-right pairs. Their behavior on larger independent sets is not constrained by that representation result, so it does not give a full edge-function circuit.
* Jukna, [Clique Problem, Cutting Plane Proofs and Communication Complexity](https://web.vu.lt/mif/s.jukna/ftp/cliq-a.pdf): the solved bipartite Research Problem 19.12 concerns communication for finding a nonedge, not the circuit-size lower bound here.
* Jukna, [Bipartite formula complexity](https://web.vu.lt/mif/s.jukna/boolean/comment20.html), February 2017: the formula model permits arbitrary functions of one side at its leaves; it is not directly the exact AO2 model of the posted statement.

## Possible additive shielding component

Prepending the `n` gates `AND(i,i)` and redirecting every original raw-input reference to its shield makes every subsequent OR reach empty. Gate references are shifted by `n`, and the output is renamed likewise. This preserves the exact function and adds `n` gates, stronger than the already checked factor-six Shield construction for this purpose. The construction is mathematical only at this point; no new Lean artifact has been built for it. If formalized, applying the posted statement to the shielded circuit would yield the conditional unrestricted bound `|E| + |S| <= C.size + n + 1`. This consequence does not prove the posted statement.

At STOP, the additive construction had been assigned to the library agent, who confirmed that no compiler source or build had started. The existing frozen `Shield.mem_orIn` characterization at `/tmp/oec/pequalnp-pilot-99/gap4970/lower_bound/Shield.lean:617` was shared as a useful interface. There were no active searches or compilers in this agent's lane and no new Lean files to preserve.
