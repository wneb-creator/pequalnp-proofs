# Independent multi-output model review

Approved for the planned finite search: no model-blocking issue found. This review concerns the shared line-variable architecture, not all possible 26-input circuits.

Reviewed script SHA256: `f89f9b68487376c9a2de238bba10551fc1b0b7076664fc62688145fe668633cd`.
Reviewed data SHA256: `673b99e94dfea3d73a5b8e006629891597310c50db198cb76a986ad4cd40fb4e`.

- **Canonical closure is sound and complete for this architecture.** Flatten every free-AND operand into inputs and earlier OR wires. Conjoining all available wires whose singleton signature contains the operand signature preserves that signature and can only decrease other truth values. Thus required positive singleton values persist and negative tests remain false. Empty-signature OR operands and comparable-signature OR branches can be deleted without worsening the tests. A witness using fewer than 38 ORs can be padded with duplicate two-input ORs: their two-element signatures do not contain any four-element target.
- **Negative pruning was independently checked.** The 468 samples are exactly the 234 three-line caps and 234 four-line caps. For each target, all smaller disjoint caps extend to a retained disjoint four-line cap. There are 54 retained negatives per target, with union size 234. Monotonicity supplies the omitted negative tests and forces truth whenever a sample meets the target neighborhood.
- **The joint false-OR bound is valid.** At each retained negative, exactly three target outputs must be false; their neighborhoods have union size nine. Joining those outputs uses two extra OR gates, both false at that row. The joined output is sensitive to all nine missing coordinates, so sensitivity counting requires eight false OR gates in total, hence at least six original false OR gates.
- **The symmetry restriction is valid.** The 39 maps `l ↦ a*l+c` with `a∈{1,3,9}` preserve incidence, target neighborhoods, and retained caps. The 78 unordered input pairs form two orbits of size 39, represented by `(0,1)` and `(0,2)`. After redundant gates are removed, the first OR joins two distinct input singleton signatures, so these representatives suffice.
- **Independent control evaluation passed.** The saved 39-OR witness was evaluated directly on all 560 cap assignments for all 13 outputs: 7,280 comparisons passed. Its gate references are backward. The fixed-baseline control bypasses the first-OR restriction; that restriction was therefore justified separately by the orbit check above.

A SAT witness at 38 ORs would yield the intended 50-OR global circuit after 13 free-AND output products and 12 outer joins. An UNSAT result would rule out this architecture only; it would not prove the posted 51-OR lower bound. No heavy search was run during this review.

Independent finite-check report: `/tmp/oec/pequalnp-pilot-62/multi-model-audit.json`; complete output: `multi-model-audit.log` in the same directory.
