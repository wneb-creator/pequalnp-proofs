# Independent review of plane helpers

Verdict: PASS for the two supporting lemmas in `/tmp/oec/pequalnp-pilot-98/2583-plane.lean` at SHA256 `8a8030d154079fe99d4ed8f27e6cc25eae5e2b0d007d9e3dd463e8b281d48825` (26 lines). Root reports the separate Lean run passed; this review did not rerun it.

`incidence_card` double-counts incident point/line pairs by lines, commutes finite sums, and substitutes the given line cardinality. Its conclusion N*(q+1) needs no additional plane axiom. `lines_unique_intersection` supposes two distinct common points and obtains equality of the two lines from uniqueness, contradicting the stated line inequality. It proves at-most-one intersection, exactly as stated; it does not claim existence of an intersection.

No forbidden token or semantic issue found. When merging into the named file, put both lemmas inside its existing `PEqualNP.Outside.L_meta_2583` namespace. The standalone scratch namespace `PEqualNP.Outside.L_meta_2583_Plane` is not an allowed helper namespace for that submission path.
