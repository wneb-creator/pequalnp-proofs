# Six-gate cone after fixing five stars

2026-11-25 UTC. Root proposed this smallest nontrivial fixed-star cut; constructive prepared and exhaustively checked the data. Solver execution and encoder review are separate.

Fix the stars at left vertices {2,3,4,5,6}. Their 15 gates plus four union gates cost 19. The remaining two stars have six edges on residual variables `[0,1,7,8,9,10,13]`. A six-gate cone plus the final OR gives `19 + 6 + 1 = 26` gates.

Four pure intermediate ORs are available at no additional cost:

* x8 OR x13, from the star at 2, wire 14;
* x10 OR x13, from the star at 4, wire 20;
* x9 OR x10, from the star at 5, wire 23;
* x8 OR x9, from the star at 6, wire 26.

These form the complete cross grid between the two private-neighbor pairs {8,10} and {9,13}. In local coordinates they are pairs `(3,6)`, `(5,6)`, `(4,5)`, and `(3,4)`. Together with the seven original residual variables, the cone has 11 correlated cut signals.

There are exactly six positive edge rows and four maximal-independent negative rows. Their sufficiency was checked over all 128 residual assignments. The fixed union is wire 32; cone internal wire 11+j maps to full wire 33+j. The final OR is wire 39 for a six-gate cone.

No pair-choice sweep is needed within this ordinary fixed-five-star family. Zeroing outside variables preserves every residual positive row and can only remove false positives. Each of fixed stars 2,4,5,6 has one outside right neighbor, so its full neighbor sum reduces to the corresponding cross sum; its first sum reduces to that sum or an existing input. Fixed star 3 reduces to original input 7 or zero. Reassociating the fixed stars produces the four pure sums at the indicated wires without changing their cost or function. Thus all useful reduced OR cuts are already present.

The seven-gate residual baseline and its full 27-gate embedding are exact. Two six-gate seeds omit original edge (0,8) or (0,7). Both residual functions were checked on all 128 inputs, and both full 26-gate embeddings were checked on all 16,384 inputs against the corresponding edge-deleted graph. Each has 47 false negatives against Heawood and no other errors. Neither is a witness.

The eight residual automorphisms swap the two centers and independently swap each private-neighbor pair. Their action on all 11 signals was checked on all 128 assignments. The optional symmetry file lists 17 first-input-pair orbits including repeated operands.

Stable artifacts under `/tmp/oec/pequalnp-pilot-70/constructive/`:

* `five_star_cut_cone.py`
* `five-star-cut-cone-rows.json`
* `five-star-cut-cone-baseline7.json`
* `five-star-cut-cone-seed6-missing-0-8.json`
* `five-star-cut-cone-seed6-missing-0-7.json`
* `five-star-cut-cone-symmetries.json`

Reproduce with `python3 five_star_cut_cone.py --output-dir <the scratch directory>`. Only the Python standard library is used; the full preparation and validation took under one second in the current environment. No solver result is claimed in these preparation notes.

A separate bounded formula dynamic program, `small_formula_dp.py`, completed in 0.297 seconds and settled all 1,024 signatures on the ten boundary rows. With the 11 cut signals as free leaves, the minimum formula gate count is seven. Trying 147 target-root decompositions and merging equal intermediate signatures in the single stored representation of each function still gave seven gates. Result: `five-star-cut-cone-formula-dp.json`. This is not a circuit lower bound: a six-gate DAG might use different intermediate representations or sharing not captured by this formula dynamic program. The SAT circuit search remains necessary.
