# Independent partial review 02

Reviewed 2026-11-25T14:00:47.798280+00:00

Source: lean/PEqualNP/Outside/L_meta_2592.lean
SHA-256: cd9e691a5d8d02508b875c3e712fc7e91610449e788071a4e420b06b0f330f8d
Lines: 101

Verdict: PASS for a partial-result push, subject to the named module build passing. This is not a completed proof of L-meta-2592 and is not ready for a proof PR or acceptance claim. The file deliberately has no final theorem with the posted statement.

The diff adds three Mathlib imports and three helper lemmas within the required namespace. The first lemma correctly compares the original-input assignments i=false and i=true. Since H ignores that coordinate, monotonicity of x ↦ H(x,¬xi) yields H(x,true) ≤ H(x,false); monotonicity in H’s final bit gives the reverse inequality. The replacement lemma uses that equality, and the non-computability lemma contradicts an explicit dependence witness for a monotone target. All assumptions needed for these conclusions are explicit; no claim is made for circuits where the original input also reaches H.

Format checks: imports only at top; permitted Mathlib modules; helpers inside namespace PEqualNP.Outside.L_meta_2592; no forbidden root substring, quotes, proof holes, new axioms, native evaluation, attributes, or compile-time commands. Existing limit options are declaration-local and allowed. The existing graph bounds are unchanged.

Build status: root is running the named module build; this review did not rerun it or the checker.
