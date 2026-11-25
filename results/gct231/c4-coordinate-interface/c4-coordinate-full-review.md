# Full C4 coordinate interface: source review

The frozen `fresh/C4CoordinateInterfaceFull.lean` snapshot, SHA256 `22de414e9c8b8b992ce11a46d8167da4f09d86ddafc71f29e7bbd84317e317fe` (10351 bytes), passes source review. The full source preserves the independently checked scaled matrix and corrected quadratic/cubic formulas. The actual matrix is scaledMatrix/8, so its line-polynomial coefficients are Q4/4 and C16/16. The formal polynomial identity follows from the pointwise permanent expansion by polynomial extensionality over C; the explicit evaluation simplification uses only sum/product and evaluation rules.

A line with permanent constantly 24 therefore has Q4=C16=0. At e=0, C16 is 2(fab−HXY), giving fab=HXY. The reconstruction lemmas are preserved verbatim from the supplied additions: every symmetric matrix with entries 02=13=0 and total entry sum zero is the actual matrix at the seven stated coordinates. No nondegeneracy, nonzero-coordinate, or unproved normal-form assumption is added.

The author build `fresh/c4-coordinate-full-build03.log` is empty and passed with exit 0 (approximately 14.73 seconds, peak 2675068 KiB). This independent pass was source-only and did not start another compiler. Earlier exact Ryser and matrix-entry verification is documented in `c4-scaled-interface-review.md`.

Review completed 2026-11-25T11:42:51.872610+00:00. This supplies a coordinate/coefficient interface, not an exclusion of all C4-supported three-planes.
