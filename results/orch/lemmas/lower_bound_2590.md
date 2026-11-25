# L-meta-2590 structural route

2026-11-25 15:20 UTC. This is research progress, not a proof of the posted statement.

The P9 restriction route gives a monotone floor of 18 globally and 19 when the first normalized binary operation is an AND. It does not yet give 20. Charging duplicate nonconstant projected signals is unsound, including in the monotone model. Deleting a clean edge block and its OR reader also does not automatically leave the exact edge-deleted graph: the residual may still accept the deleted edge or larger sets containing it.

The new route uses the generic strict-live DAG framework extracted by library_route from L_meta_971. In an alleged size-19 Petersen circuit, the surplus is at most 10. If all 10 vertices are eligible, all available surplus is reserved for one pure singleton-support branch per vertex. Consequently Bzero and residual units vanish. The generic sem_code_count bounds every consumption code by two positions, with any carrier merges reducing that bound further.

The following finite code constraints are NOT sufficient for a contradiction:

- Each vertex has at most two consuming positions, with no position and its opposite in the same code.
- Every Petersen edge has opposite positions in the codes of its endpoints.
- For distinct x from a,b and nonadjacent a,b, the code of x is not contained in the union of the codes of a,b, including a=b.

Counterexample agent checked an explicit code model, with opposite position p given by p xor 1:

W0={1,2}, W1={1,3}, W2={0,8}, W3={1,4}, W4={0,10}, W5={0,12}, W6={0,14}, W7={1,6}, W8={1,5}, W9={1,7}.

It uses 20 memberships, 12 active slots and 8 pair IDs. Let A={2,4,5,6}; its complement B induces the matching (0,1),(3,8),(7,9). Slot 0 is shared by A, slot 1 by B; all other slots are private. The model covers the 15 graph edges and 12 false-positive pairs. Every code has a private slot, which makes all cover-free conditions hold. The computational checks are in gap2590/counterexample/code_model.json and code_model.py under the scratch root.

A previous candidate with slot graph consisting of two pentagons was also exhaustively checked: 945 pairings, 295 satisfying within-code exclusion, at most 11 of 15 graph edges covered. This is a computational observation only.

An attempted temporal rejection of the code model failed. The tempting argument fixes x in A and compares pair assignments {x,b} over b in B, treating the three B-private matching AND gates as always false. However a B-private operand can also OR in earlier AND outputs. After the shared A/B gate fires, a B-matching gate can distinguish the B choices. Thus the claimed constant-trace induction is invalid. A distinction-count or an actual AND-skeleton proof is still needed.

Static counting alone does not repair the gap: 8 pure OR gates + 8 empty-support AND gates + 3 final OR gates can total 19 because the four private-A filters may consume earlier empty outputs. Counting every filter as a separate final root would incorrectly give 23. The problem is the edge loss through those filters, not bare connectivity.

Existing L_meta_8775 and L_meta_905 exclude a relaxed Petersen AndCount circuit with at most six AND gates and at most two raw-variable occurrences in AND operands. Their extra six-AND bound is material. Counterexample agent is probing whether the relaxed seven-to-ten-AND cases are satisfiable before we attempt to use this route.
