# Exact QQ membership DAG hook map

Read-only architecture review of msolve v0.11.0 commit cc044551f8e202d00691990fd3fd0b1226a88ea2, with the separately documented pivot-count fix. No certificate instrumentation has been applied. Line numbers below refer to pristine `msolve/src/neogb/`; the patched `qqfix/la_qq.c` has small offsets.

## Minimal invariant and certificate language

Associate every live basis or matrix row polynomial P with a stable DAG node proving P is in the ideal of the original input polynomials. Four node operations suffice: Input(i); MonomialMultiply(parent, exponent vector); ScalarMultiply(parent, rational); and AddScaled(parent1, rational1, parent2, rational2). Exact rational scalars are serialized as integer numerator/positive denominator. Use monotone node IDs independent of recycled row pointers and coefficient slots.

A final nonzero constant c yields `1 = (1/c) P`. Retain only ancestors of that final node. Independent verification should replay all retained node identities using sparse exact rational polynomials, checking against the original input file/hash and each recorded output polynomial. Lean can then prove each retained identity with `ring`/`linear_combination`, or verify a flattened rational combination if it stays small. A solver unit-basis status alone is not a certificate.

## Input and initial basis

* `io.c:252 import_input_data`, especially its QQ branch at375–400: every input polynomial is multiplied by the product of its term denominators. At this point input generator i is assigned coefficient slot ctr. Register `ScalarMultiply(Input(i), product_denominators)` before sorting. The input terms in this job have denominator1, but the reusable wrapper permits rationals.
* `engine.c:96` sorts the `bs->hm` pointer array; keep provenance attached to stable `COEFFS` indices or row identity, not current array position.
* `engine.c:103` calls `basis.c:466 remove_content_of_initial_basis`. It removes coefficient gcd and normalizes leading sign. Record the exact nonzero leading-coefficient ratio after/before for each polynomial to obtain its rational scale; this handles signed single-term content and conditional early exits safely.
* `io.c:1046 normalize_initial_basis` is a no-op in characteristic0, but that does NOT replace the preceding content removal in engine.c.

## Symbolic matrix rows

* The universal monomial-multiplication hook is `hash.c:1369 multiplied_poly_to_matrix_row(sht,bht,hm,em,poly)`. It receives source `poly[COEFFS]` and the exact multiplier exponent vector `em`. Register the new row pointer with a monomial-multiple node of that source basis node.
* It is called by `symbol.c:200 select_spairs_by_minimal_degree` (actual calls around327,362), `symbol.c:493 find_multiplied_reducer` (call539), and the other selection paths. Hooking the common constructor covers them without relying on selection-order details.
* `BINDEX` and `MULT` metadata are populated only when `trace_level == LEARN_TRACER`; direct QQ runs use NO_TRACER. Do not treat those fields as valid without changing that contract.
* Hash exponent vectors contain degree slots. Serialize only variable exponents exactly as `io.c:578 export_data` does: skip index0 and indexebl. Never serialize the raw whole `em` as a variable exponent vector.
* `poly_to_matrix_row` represents multiplier1, used by final basis reduction (`f4.c:590`) and other matrix construction. It needs a copy-of-parent hook too if those paths are traced.

## Active rational row reduction path

`io.c:878 linear_algebra` dispatches QQ option2 to `la_qq.c:770 exact_sparse_linear_algebra_qq`, then to `la_qq.c:567 exact_sparse_reduced_echelon_form_qq`. The primitive elimination function is `la_qq.c:258 reduce_dense_row_by_known_pivots_sparse_qq`. The option1 ab-first variants are outside this configured path.

The primitive reducer sees the current dense row R and pivot row P at column i. If the current coefficient a is divisible by pivot coefficient b, it performs `R := R − (a/b) P`. Otherwise it computes l=lcm(a,b), u=l/a, v=l/b and performs the polynomial operation `R := u R − v P`. Record those exact integer u,v before GMP temporaries are reused. Explicitly use u=1 in the divisible branch: the C variable mul1 may retain an earlier value and is not assigned there.

The routine has already moved some surviving terms from `dr` to `cf`. Its lcm branch scales both the saved `cf` terms and the unresolved part of `dr`. The polynomial invariant is the combination of both buffers. Consumed pivot entries in `dr` can contain stale values after elimination; they are logically discarded as the loop advances. Do not interpret the entire raw dense buffer as the current polynomial without respecting this representation.

Pivot provenance depends on column: for i<ncl it is an old symbolic reducer row backed by `bs->cf_qq[dts[COEFFS]]`; otherwise it is a new matrix pivot backed by `mat->cf_qq[dts[COEFFS]]`. A row-pointer map plus separate basis-coefficient and matrix-coefficient sidecars avoids confusing these two namespaces.

`la_qq.c:567` initially expands each selected symbolic row into drl, then calls the primitive reducer. Capture its initial node before `free(npiv)` (around637). On successful reduction, assign the result node to both the new row and matrix coefficient slot. On zero reduction, a zero polynomial node may be discarded unless needed for debugging. Serial mode makes the concurrent insertion retry branch inert, but preserve the existing node correctly if a retry is ever enabled.

`la_qq.c:24 remove_content_of_sparse_matrix_row_qq` is called after newly found pivots and after interreduction. It divides gcd and possibly flips sign. Record an exact scalar ratio from before/after the leading coefficient, as with initial normalization. This function receives coefficients only, so the caller should supply/update the associated node, or a coefficient-pointer map must track it.

The same primitive reducer is called while interreducing new pivots near714, and by `interreduce_matrix_rows_qq` near858. Each dense reconstruction preserves the corresponding old node. Any `mpz_swap` or memory compaction alone is a representation change, not a polynomial operation.

## Inserting basis elements and stopping early

`convert.c:634 convert_sparse_matrix_rows_to_basis_elements` transfers each new matrix polynomial into `bs` at slot bl+k. Before `rows[i][COEFFS]` is overwritten at693, copy the matrix coefficient-slot certificate into the basis certificate sidecar. Reverse insertion order under sort=-1 must be mirrored.

The conversion detects degree0 at698 and sets `bs->constant=1`. This is the shortest endpoint for a unit-ideal certificate: emit the constant polynomial and its DAG node immediately, before final interreduction and basis storage cleanup. No need to trust later reduced-basis export for that certificate. Root can choose whether the solver continues normally after this snapshot. The update loop detects the same constant and ends F4.

`f4.c:570 reduce_final_basis` builds another symbolic matrix, reduces it, frees prior basis elements and reinserts rows. If the certificate is instead taken only at final output, all these pointer/slot changes must be traced, including `poly_to_matrix_row`, exact QQ reduction, and conversion. Capturing the first constant avoids this additional bookkeeping.

## Suggested staged validation

1. Instrument only this serial, exact QQ, option2 route in a separate source tree; preserve the current tested engine.
2. Run the three QQ controls. Replay every emitted local identity independently and ensure each final reduced basis polynomial is certified. Use the unit control to verify normalization to1.
3. Run the already solved smaller rowzero system, compare its exact contradiction with the independent OpenF4 certificate, and produce a small Lean replay.
4. Only then repeat a successful full chart run with tracing. Prune the constant-node dependency DAG before expansion/Lean emission.

Existing modular `trace_t` data describe symbolic/reduction schedules for replay at other primes. The public export_f4 API returns polynomial coefficients but does not expose this ideal-membership DAG. No automatic certificate export has been verified.
