# Exact Boolean rewrite searches

The order-three scripts use the 52 incident pairs and the 704 maximal independent assignments from the repository's counterexample_q3_repair.py. The output is a monotone function, so agreement on these tests implies agreement on every input.

The single-wire search pins a gate to zero and one to compute where the output requires its value. Replacements can draw from any wire independent of that gate. They include one gate, two gates, and products or sums of two gates. The search estimates the live cone size, rebuilds the circuit with structural hashing, and validates the entire output before accepting each step.

The joint search pins two gates independently. Required positive and negative values on each replacement eliminate impossible expressions. Remaining coupled positive tests require their disjunction, and remaining coupled negative tests forbid their conjunction. The decoded circuits are checked against the same boundary. Both searches sample candidates and bound the retained candidate lists.

Run the files with Python 3 from this directory or with the repository's results/orch/search directory available. The seed program also reads its q3-concurrent-control/control.json archive.

| Program | Seed | Wall-time cap | Output |
| --- | --- | --- | --- |
| exact_rewrite.py | 76131 | 540 seconds | run.log |
| joint_rewrite.py | 76132 | 500 seconds | joint.log |
| two_pencil.py | 76134 | 242 seconds | two-pencil.log |
| affine.py | 76135 | 245 seconds | affine.log |

The direct65-control.json file records a 65-gate order-three circuit obtained by replacing the distributed three-gate expression with one AND and one OR. It has zero boundary errors and requires a repeated leaf exactly on edge (6,23). A canonical 64-gate circuit computes the same function.

The two-pencil module has four rows and four columns. Its point inputs are the sixteen intersections, one common point for the rows and one for the columns. The incidence function has 40 positive pairs and 228 maximal independent negatives. In PG(2,4) these are the eight complete lines through either of two points, excluding their join. Adjoining the thirteen remaining line stars costs 78 gates. The canonical module has 47 gates and yields a 125-gate plane circuit. Among the omitted center labels, any nonempty row set together with any nonempty column set is closed, giving 225 possibilities. The other three are empty, all rows and all columns.

The affine module uses the nine points off Singer line zero in PG(2,3) and the twelve remaining lines. It has 36 positive pairs and 197 maximal independent negatives. The missing four point stars add 20 gates. The canonical module has 44 gates and its decoded 64-gate full plane circuit passes all 756 boundary checks. A set of omitted affine point labels is closed exactly when it is a union of affine lines. The 130 subsets of size six or more are all closed because at most three missing points can obstruct the four lines through a retained point. The smaller closed sets are the empty set, 12 lines, and 54 unions of intersecting line pairs.

The affine search favors rewrites that meet the proposed size-43 bounds on present neighborhood ORs. It identifies present wires by testing every singleton and the complementary maximal false point or line assignment for each neighborhood. Some seeds distribute stars before searching to reduce the initial number of present neighborhoods.

These heuristic searches provide upper bounds for validated candidates. A matching lower bound requires a separate proof.

The four runs sampled 131,399 cuts across 2,259 starts. Minimum exact sizes were 64 in both full-plane order-three runs, 47 in the two-pencil module, and 44 in the affine module. The smallest affine circuit found that met the present-neighborhood conditions had 46 gates. The independent scalar replay in audit_controls.py enumerates every center subset for each saved control.
