# Lower-bound route for L-meta-2592

Checked source inventory (all from current main):
- R_meta_2592_271: reduction to binary floor `15 + notCount C ≤ C.size` plus the 1–4 NOT case.
- R_meta_2592_318: reduction to last-NOT decomposition plus a separator lower bound.
- R_meta_2592_408: reduction to legal normalized/output-last circuits plus their lower bound.
- L_meta_4725 (3224 lines, imports only Mathlib and Defs): proves the binary floor. Its route compresses into a minimal clean circuit and uses six required branching wires; counting yields at least 15 non-NOT gates.
- L_meta_6194: essentially the same 15-binary-gate bound with countP statement.
- L_meta_9818 (7810 lines): proves a 13-edge ten-vertex subgraph has no circuit of size ≤16. It embeds a full finite-search proof that Petersen-minus-one-vertex requires >15 gates, then removes a pendant vertex.
- L_meta_7493: Petersen-minus-one-vertex needs at least 14 non-NOT gates; useful with restrictions preserving enough negations.
- L_meta_8775 (514390 bytes): excludes a six-AND compressed circuit subject to at most two direct reads per input; close to the file-size cap and narrower than our arbitrary-NOT case.
- L_meta_8127: an edge gate supplied for free still requires ≥10 additional gates, too weak for the target.

Promising but unproved route: use the exact Petersen-minus-one-vertex lower bound (>15 gates) and force a restriction removing ≥4 gates in every ≤19 circuit containing a NOT. Presently no theorem establishes that removal count. Merely counting input reads removes only one to three gates and is insufficient.

No stronger checked theorem directly closes the full target. Three reductions for 2592 already occupy all slots, so a fourth reduction is unavailable under the stated cap.
