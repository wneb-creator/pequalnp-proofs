# L-meta-1896 mathematical assessment

The incidence relation is PG(2,3), with 26 inputs, 52 incident pairs, and no bipartite 4-cycles.
Exhaustive Python census over all8192 point subsets found704 maximal independent sets.
Exactly468 meet the posted generic restriction:234 of type(3points,4lines),234 dual.
The3-point sets are noncollinear triples;4-point sets are quadrangles.
Every nonincident/uniside pair (273 total) is contained in a generic false input, as is every singleton.
Thus monotonicity and the posted promise force exactly the52 incident pairs as quadratic minterms.
The excluded236 maximal independent inputs have size types:
(0,13):1; (1,9):13; (2,6):78; (3,3):52; (6,2):78; (9,1):13; (13,0):1.
Higher-degree minterms are allowed, including triples of collinear points and triples of concurrent lines.
This prevents directly replacing the promise by full graph-function equality.

Existing reductions:
- R_meta_1896_52: compile circuits to a shared sequence of binary merges on52 positive edges; geometry of16 symmetry orbit seeds; a50-merge obstruction remains the hard part.
- R_meta_1896_347: reduce false tests to36 cyclic-orbit seeds (36*13=468), plus unproved finite bound.
- R_meta_1896_1: dualize with a true sentinel and compress freeORs into AndCountCircuit; targetANDcount51 is still the hard part.
Sibling1898 is checked in7334lines but supplies the separateANDcount side, not the missingORbound.

A potentially useful normalization for exploratory synthesis: with AND gates free, every OR gate can be written as an OR of two conjunctions of inputs and earlier OR gates; final output is one conjunction. This preserves OR count and eliminates all unbounded AND topology. Script or_normal.py encodes this exactly over specified finite rows. Constants are included. For6-cycle,4ORs are UNSAT both on all assignments and on only weight<=2 assignments;5ORs are SAT (positive control). Fano21-edge graph with19ORs on only weight<=2 assignments timed out after30seconds. These SAT observations are exploratory, not Lean-checked.

No general checked OR>=edges-1 lemma was found. A proof from exact quadratic minterms plusC4-freeness would solve the task, but arbitrary AND filtering and shared intermediate ORs are the obstacle: an intermediate complete rectangle can contain nonedges that later AND gates remove, so a naive biclique-star charge is not yet valid.

Conceptual obstruction to using only quadratic minterms: For large primeq, affine-plane incidence hasq² point inputs,q² line inputs,q³ edges and no4-cycles. Onehot point/line addresses can be encoded in dual-rail binary withO(q²logq) ORs, then incidencey=ax+b modq evaluated by a polylogarithmic Boolean arithmetic circuit converted to dual-rail monotone gates. ANDing left/right-presence flags suppresses weight<=2 same-side inputs. This gives a monotone extension with exactly the desired quadratic minterms but unconstrained higher-degree values, asymptotically fewer thanq³-1 ORs. Consequently a universal quadratic-C4free ORbound is false in this unrestricted-extension setting; the468 generic negative inputs are essential. This is constructive asymptotic reasoning, not a Lean-checked q3 counterexample.

Additional freeAND normalized SAT probe: theta333 graph (three length3 paths between common endpoints;8vertices9edges,C4free),7ORs, pair-only rows: UNKNOWN after30seconds. No counterexample found. All generatedsolverlogs are retained; unknowns are not lower-bound evidence.
