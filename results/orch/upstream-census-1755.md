# Fresh upstream circuit census

Read at 2026-11-25 17:54–17:57 UTC. The parent exported353 new Outside
Lean files between base `2d2cdadb1c632bf58df2cb0dff0d650156a0e0b4`
and exact upstream head `ed419030b2f93e3f357003611f865f28e436bd9a`.
No upstream files were merged, built, or copied into this branch.

The scan discovered all353 filenames first, then extracted the final
fully qualified theorem statement from each. All353 extracts have balanced
parentheses/brackets/braces and no internal let assignment. Every circuit
final specializes to a concrete finite function; none is a generic circuit
normal-form theorem and none has Fin13 or Fin26 in its final statement.
Most are six-input truth-table circuit bounds or monotone-versus-general
size comparisons. The only fully generic final after excluding concrete
Fin/testBit/HasCircuitSize instances is the unrelated polynomial refutation
L_gct_273.

A second pass selected38 non-table circuit files and used bounded searches
for hoist, dirty, clean, normal, IsRead, ReadK, ReadTwo, TopForm, andCount,
degree, triangle, and bipartite. Eight files matched. The relevant helpers
were `normalize_strictLive` in L9732/L9789/L9774 (existing circuit
normalization), and generic signed-gate normalization in L12000, explicitly
adapted there from accepted L11167/L5459. Other clean/normal hits concerned
no-NOT case splits or finite bitvector normalization. No new clean/dirty
AND/OR structural theorem emerged from this bounded keyword scan.
L9774 was separately assigned to proof_route for detailed inspection.

This is a bounded source census, not a proof that no usable theorem is
present. Complete extraction and bounded-match records remain in the
job scratch directory under not-elimination/upstream-1755-*. The active
four-stratum search source and its624-seed pool were unchanged.
