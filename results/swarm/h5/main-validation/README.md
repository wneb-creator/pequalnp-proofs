# Main helper validation

The named helper source at `cc06910dad6d57c83b639802d4c71034de91063f` built successfully with `lake build PEqualNP.Outside.L_meta_2373` using Lean 4.36.0 and the cached Mathlib dependencies. Complete build output is preserved. `FinalPublicAudit.lean` elaborates 75 separately stated expected theorem types and prints their recursive axiom dependencies; the complete audit output records only `propext`, `Classical.choice`, and `Quot.sound`.

The source proves counted restriction and renaming lemmas, cofactor bounds, raw-input reader bounds, and a 47-function residual classifier. It does not prove or refute the full posted gap. This is a helper branch, with no PR and no official acceptance verdict. The final source has 524205 bytes, below the 524288-byte submission cap; this size observation is not a claim that this partial payload qualifies as a final submission.

The independent source review was written before the final build and therefore says the build and audit were pending. Both subsequently passed, as recorded by the complete logs and artifact hashes in this packet. An earlier broad export-census concern was corrected after reading CheckLemma: the blanket reduction-extra check applies to REDUCTIONS; ordinary full-lemma checking skips matching imported theorem equations. No blanket rejection of this helper source is claimed.

These files are research validation artifacts. They add no imported proof assumptions to the helper source. `FinalPublicAudit.lean` imports the named helper module and can be replayed after building that module. The manifest pins the exact reviewed source and complete saved artifacts.
