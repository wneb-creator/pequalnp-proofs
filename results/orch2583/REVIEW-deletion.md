# Independent review of Deletion.lean

Reviewed UTC: 2026-11-25T14:53:20.393400+00:00
Reviewer: status_check; author: lean_setup. Reviewer did not author or modify this proof.
Input: results/orch2583/lemmas/Deletion.lean
SHA256:9aac0235e290a080ad046fd0bef8644ebb01987d3962099e1836adb3481f39be
Size:4,757bytes;104lines.

Verdict: PASS semantic and source-format review for a partial checkpoint. This is a combinatorial helper, not the posted L-meta-2583 theorem.

The four lemmas have the stated strength:

1. `restricted_card_left` counts incidences whose point belongs to P as |P|*d under row-regularity. The fiber bijection maps an edge to its line and has the needed injectivity from the fixed point coordinate.
2. `restricted_card_right` proves the dual count under column-regularity; its product-coordinate injectivity is correct.
3. `cover_after_deletion_count` bounds N*d by (|P|+|L|)*d+|U| whenever P∪L covers every incidence outside U. The covering inclusion and two union-cardinality upper bounds permit overlaps and are sound. U is not required to be a subset of incidences; allowing extraneous pairs only weakens the bound and is harmless. No simplicity, C4-free, or projective-plane hypothesis is needed.
4. `cover_after_deletion` derives N≤|P|+|L|+floor(|U|/d), correctly requiring d>0. Integer division direction uses `Nat.le_div_iff_mul_le`; the natural subtraction and final addition commutation preserve the exact floor bound. The d=0 case is intentionally outside this final lemma, while the preceding count lemma still covers it.

Source format: imports only PEqualNP.Defs on the import line; all declarations in PEqualNP.Outside.L_meta_2583.Deletion. No sorry, axioms, native_decide, forbidden identifier text, string literals, attributes, or set_option commands. Source is well below512KiB; assembled named-file size and allowed final target statement remain the parent reviewer’s integration checks. No secret-bearing data is present.

Validation evidence: root reports successful standalone compilation. Existing logs `/tmp/oec/pequalnp-pilot-103/2583-deletion-second.stdout` and `.stderr` are both empty. Reviewer did not rerun compilation. The subsequent assembled-file build remains pending and is required before a claim that the assembled checkpoint compiles. This partial has no exact final target theorem, so it must not be presented as a completed proof PR.
