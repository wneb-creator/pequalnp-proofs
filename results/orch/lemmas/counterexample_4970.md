# L-meta-4970 counterexample and semantic checks

Parent alone holds the lease. Exact statement is in desk-poll-003.json. No counterexample to the posted conclusion has been found.

## Definitions and edge cases

`TopForm.IsAO2` requires AND/OR gates, exactly two operands, and all references strictly backward. It permits unused gates and repeated operands. Constants and forward-reference tricks are excluded.

`TwoColour.tCount` counts OR gates whose OR-only reach contains both a raw point and a raw line. AND gates reset this reach to the empty set. Consequently ORs combining already-computed edge products are not counted as mixed.

For an empty edge set the conclusion holds with the empty cover, regardless of the circuit. A component consisting of a single isolated edge cannot satisfy the pure-star hypothesis: both endpoints have degree one, while every witness must contain at least two neighbors. Invalid output wires cannot compute a nonempty edge function.

## Unused witnesses invalidate a direct consumption inference

The hypothesis only asks that the semantic pure-star OR occur somewhere in the gate list. It does not require the witness to reach the output or feed an AND with its center.

A minimal illustration uses p=1,l=2 and both possible edges. Gates are AND(0,1), AND(0,2), OR(3,4), OR(1,2), with output wire5. The last OR is an unused star witness for both edges. All posted premises hold, but no AND consumes that star OR. The posted lower bound remains true.

## Counterexample to the stronger all-components ledger

`gap4970/counterexample/dead_star_ledger.py` exhaustively verifies a bipartite six-cycle example on all64 inputs. The circuit consists of the usual8-gate all-point-star realization followed by3 unused opposite-side pure-star ORs. It has no mixed ORs and satisfies the exact star-witness condition for every edge.

Classify every OR gate that semantically computes OR(Q), with |Q|≥2 and Q contained in a unique center's neighborhood. Group these supports into overlap components separately by center. In this example:

- pure-star OR gates:6;
- components K:6;
- total component leaf incidences d:12;
- minimum vertex cover tau:3;
- remaining gates:5.

Thus the proposed stronger inequality remaining≥K+tau−1 is false:5<8. The posted conclusion survives: E.card+tau=9≤12=C.size+1. This is a counterexample to an auxiliary ledger only, not to L-meta-4970. It indicates that a proof must select or discount witness components rather than charge every available component as if it were consumed.

Full circuit, truth-table checks, reach computation, semantic star classification, components, and minimum-cover enumeration are recorded in `dead_star_ledger.json` and complete stdout/stderr beside the source. No Lean proof has been claimed for these computational checks.


## Stronger pure-OR building lemma tests

A different, promising per-center ledger survived exhaustive finite checks. For each fixed input set S, count OR gates false on the assignment that activates exactly the complement of S, and accepting at least two singleton inputs. For all semantic pure-OR root supports Q⊆S, that count was always at least |union Q| minus the number of overlap components. Adding roots cannot reduce this rank, so taking every available pure root tests every subfamily.

The C++ checker exhaustively tested17,244,252 AO2 circuit prefixes on3 inputs through5 gates, and1,437,020 prefixes on4 inputs through4 gates, for every nonempty S. Repeated inputs and AND-mediated pure roots were included. No counterexample was found. This supports sat_encoding's proposed lemma computationally; it is not a general proof. Source and complete logs are frozen in auxiliary-checks-manifest.json.

A clean potential proof invariant was sent to sat_encoding: build a graph on S using at most one new edge per counted OR, so every gate false at complement(S) has all its accepting singletons inside one component. At AND choose an operand false at complement(S), whose singleton support contains the output's. At OR both operands are false there, so at most one edge joins their support components.

## Generic AND-count probes

Free-OR skeletons model each AND operand as an arbitrary OR of raw inputs and earlier AND outputs; output is an OR of AND outputs. There are no raw-read or singleton-rejection restrictions. C6 with at most2 ANDs is computationally UNSAT; a fixed3-AND control passes all64 inputs and expands to8 binary gates. Fano with7 ANDs has a fully verified27-gate control. Fano with at most6 ANDs returned UNKNOWN after30 seconds, both unrestricted and with monochromatic raw supports modeling tCount0. No general AND-count theorem follows from these checks.


## Further bounded probes and transfer check

Unrestricted exploratory circuit searches for C8 with10 gates and subdivided K4 with14 gates each timed out after30 seconds. Their canonical11/15-gate controls pass all256/1024 inputs, have Tcount0, and provide semantic star ORs for every edge. Both graphs are C4-free and have minimum vertex cover4 by exhaustive enumeration. The search models use connected gates, distinct sorted operands, and a colex order; no T0 or star-witness restriction is imposed. No conclusion follows from the timeouts.

The hiding transfer proposed by lower_bound is semantically valid. Replace OR(u,v) by AND(u,u),AND(v,v),OR(copies), renaming later references. Every new OR has immediate AND operands, hence empty raw OR reach and Tcount0. For even left degrees, append a dead monochromatic OR for each pair in a partition of every left neighborhood. This adds |E|/2 gates and supplies exactly the posted star witnesses. Total size is C.size+2*ORcount(C)+|E|/2≤3*C.size+|E|/2. Consequently the posted theorem would imply |E|+2*tau≤6*C.size+2 for arbitrary original AO2 circuits on such graphs.

`hide_or_transfer.py` validates the construction on a C6 circuit with a live mixed OR:14 gates,10 ORs,Tcount3 become37 gates after3 dead pair ORs,Tcount0. All64 assignments preserve both the output and every renamed original wire, and every added star witness is exact. This is a finite check of the transfer, not a refutation of4970 or a formal lower bound.


## Literal restriction induction obstruction

At sat_encoding's request, `restriction_obstruction.py` checks canonical C6 plus three absorption masks F∧(F∨Q), one for each existing star OR Q. The resulting14-gate circuit satisfies every posted premise on all64 inputs. Setting any vertex to zero, performing exact constant/idempotence folding, and removing every gate outside the output cone saves exactly2 gates. Each vertex has degree2 and the cover number drops from3 to2, so all six vertices fail the proposed degree+cover-drop saving3. Retaining all surviving star-witness roots does not change the savings. The broadened W-based step requires3 for point deletion and5 for line deletion; all six fail that step too. Absorption cleanup/global minimality may repair the strategy; this example only refutes the literal elimination rules, not4970. Source/result/logs are frozen in restriction-obstruction-manifest.json.

## Main-statement stochastic portfolio

Prepared five C4-free graphs with independently computed minimum covers: subdivided K4, an irregular11-vertex incidence graph, Fano minus an incident point-line pair, Fano minus a nonincident pair, and the explicit cubic16 graph G(8,3). Target gate counts are14,17,20,19,30, respectively, one below their posted bounds. Fifteen positive controls (canonical stars and two distributed variants per graph) pass complete truth-table, AO2,T0,semantic star coverage, and exact cover checks in an independent Python implementation.

The stochastic search permits unused gates, repeated operands, and arbitrary valid output wires. Fitness checks the complete edge/maximal-independent boundary, exact OR-only mixed reach, and exact semantic star coverage. The latter uses singleton supportQ and evaluation at complement(Q), which characterize OR(Q) for monotone gates. Any potential success receives a complete full-input check before reporting. Source/controls are frozen in stochastic/presearch-manifest.json; STOP-aware source versions are in stochastic/stop-aware-manifest.json. The one-CPU20-minute portfolio began16:11UTC and checks the parent gap STOP file at regular iteration/time checkpoints. No counterexample has been found so far.


## Variable-graph search preparation

A second engine derives the bipartite graph H from the output's point-line pair assignments on a fixed5+6 input universe. It evaluates all2048 assignments, rejects nonquadratic output behavior, checks C4-freeness, and computes an exact maximum matching together with a same-size covering vertex set. It retains the output cone plus enough semantic star-witness cones to cover every H edge; Tcount and gate cost are recomputed on that retained ancestor-closed circuit. Greedy witness selection can overestimate the best pruning cost, but cannot create a false counterexample.

Ten seeds include four independently verified equality circuits from lower_bound's postprocessing and canonical/distributed controls. Isolated unread raw inputs are removed and the seeds embedded into5+6 inputs. Every saved control passes an independent full2048-row Python check, exhaustive minimum-cover computation, and explicit matching/cover certificate checks. Equality seeds all have ANDcount=tau and ORcount=|E|−1; distributed seeds use one or two extra ORs. No general counting lemma is asserted. Frozen source, reproducible seed provenance, controls, and full logs are in variable/presearch-manifest.json. This engine remains a heuristic witness search, not a complete solver.


## Final cancellation and preserved search status

The root renewal returned HTTP410 around16:30UTC. The gap STOP file terminated the last fixed-graph phase at16:30:10; its recorded child/driver exit is75. The first four phases completed normally. Across all five phases the engine attempted2,896,166,912 mutations in1134.77 seconds; every best star/T0-valid candidate still missed two positive edge assignments, and no counterexample was found. Complete logs, all best/final candidates, and every extracted star/T0-valid improvement snapshot are preserved. The cancelled cubic16 phase has six frozen snapshots but received no new postprocessing after STOP.

The variable-graph engine was **never launched**. Its reviewed source, ten reproducible equality/distributed seeds, twenty complete seed/control checks, and explicit matching/cover certificates are preserved. The supplemental launch driver was independently reviewed too. No mathematical search continued after the root STOP. Final preservation manifest: counterexample/final-search-manifest.json.
