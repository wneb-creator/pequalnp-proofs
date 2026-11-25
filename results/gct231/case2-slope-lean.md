The case2 nonzero-slope boundary is now Lean checked. Frozen `case2-necessity/Case2SlopeBoundary.lean` has SHA256 `707e23e11549155ca65fe3d04b607d29d0d0173a277ccafef1c4a5b3c27f5480` (7,106 bytes). It proves that the actual scale equation F=0 and P*B*W≠0 imply rA≠0 or rB≠0, using the exact reviewed reduced-slope definitions. No premise r=0 or nonzero slope-leading coefficient is needed.

The proof uses explicit polynomial norm identities and integer Bézout identities, followed by an affine determinant identity. Its mathematical reduction and all certificate coefficients were independently checked in `c4-case2-slope-review.md`. The source copies the original scale/determinant/slope definitions bytewise from the existing necessity source into a separate namespace, so the two interfaces are definitionally compatible.

Pinned Lean4.36.0, `-j1`, sampled RSS cap4GiB and time cap90s: source build passed unchanged with exit0 and empty log in7.927830367s, peak2,017,940KiB. Exact source plus only a final `#print axioms` passed in7.900604480s, peak2,050,504KiB. The final theorem uses only propext, Classical.choice and Quot.sound. Full logs/status/freeze records are `case2-necessity/slope-build01.*` and `slope-audit01.*`; the driver is `Case2SlopeBoundaryAudit.lean`.

This is the nonzero-slope premise only, not the remaining normalized-resultant bridge or the main existence theorem.

Saved 2026-11-25T12:24:04.925072+00:00
