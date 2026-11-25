# Targeted follow-up diagnostics for L-meta-1735

The original reviewed `../finite/` archive is unchanged. This follow-up found no least TopForm circuit with nested junk, no separation between unrestricted and restricted minima, and no solution or refutation of L-meta-1735.

## Two capped searches

`structured_topform_sat.py` extends the earlier encoder to a supplied graph and an optional fixed prefix of ORs of raw inputs. All truth assignments are included in these runs, and every synthesized gate must have incomparable fanin functions. This is a necessary leastness condition, not a leastness certificate. Consequently these are exact-budget tests: the earlier OR-padding argument does not apply to the incomparability restriction.

- C7: ten synthesized gates, TopForm and a nested dirty pair.
- Subdivided K4: eight inputs, ten edges, girth five, minimum vertex-cover four; four fixed OR clauses followed by nine synthesized gates, totaling thirteen. This searches one structured prefix class only. A standard star circuit supplies a thirteen-gate upper bound, not a lower bound for arbitrary Boolean circuits.

Both runs reached300.00 real seconds with exit0/UNKNOWN. Neither found a model nor proved UNSAT. No search was launched after the parent requested the existing caps finish. Complete stdout/stderr logs and source are included; generated CNFs/binaries are omitted.

## Independently evaluable controls

`matching_bad_certificate.py` constructs the conjunction of all minimal vertex-cover OR clauses for a matching, placing the complement of the even transversal last. For m3/m4 the full circuits have23/63 gates. The penultimate dirty AND equals F OR the conjunction of the even inputs, so its only independent true assignment is that entire transversal; its smallest independent bad certificate has size3/4. Only the final AND is clean, so these are TopForm, and Ustar contains every matching edge. They are explicitly nonleast: ordinary matching circuits use5/7 gates.

`context_bypass_check.py` confirms every OR-child bypass loses a positive edge and every AND-child bypass creates an independent false positive for both matching controls. Thus even this dual contextual irreducibility is weaker than global leastness. Full64/256 truth rows and exact per-bypass witnesses are retained.

The subdivided-K4 fifteen-gate control shares four OR clauses between a nested two-dirty-AND chain and four clean stars. Full256 semantics, girth, cover number, TopForm and Ustar={ac,bd} are checked. Every child bypass is essential despite the smaller thirteen-gate standard-star circuit.

The earlier nine-gate C5 example has three removable AND-child bypasses; every OR-child bypass is essential. A separate independent check of status_review's twelve-gate C5 example verifies all32 rows, TopForm, Ustar all five edges, all126 earlier-wire replacements changing output, and an explicit seven-gate comparator. Its source witness remains in `../status-review/c5-context-essential12.json`.

## Failed control and correction

The initial C6 omission attempt failed its assertion and is retained with its full traceback. Omitting the complement clause of the even independent triple leaves its proper pairs true as well: masks5,17,20,21 survive, so the minimum bad certificate is two. `c6-omission-correction.json` records the corrected calculation. Only the matching examples establish the claimed size3/4 certificates.

All witness results here are computational checks; none is a Lean proof of minimality. MANIFEST.json records exact byte lengths and SHA-256 hashes.
