# ForkCover independent review

Reviewed 2026-11-25 by lower_bound. PASS for 797-line source SHA256
`c17d312e94ec6e139fe41709881f95afaea812ae8ece3e7f8aaf6b90be100c23`.

The assembly contains RootCover, SelectedLabels, LiveDagSupportBound, and the
new ForkCover fragment unchanged, except for removing the latter helper
imports and adding whitespace. The complete final compile log is empty;
formalization reported exit 0. No additional build was run for this review.
The forbidden-format scan returned status 1 with no matches.

The new composition constructs F explicitly from selected children and takes
T to be the union of root labels. Dirty/base nodes have no selected children,
so the concrete label equations and child-label inclusions apply. Filtering
live vertices with empty child sets gives the leaf set. Earlier-child
closure, the explicit branching budget, liveness, and extra-arc premises
meet the checked double-leaf counting theorem exactly. The dirty leaf gets
at most two labels and all other leaves at most one.

RootCover then proves coverage of every accepted root pair. Its label and
root-union premises are discharged by the constructed F and T; no coverage
conclusion is assumed. The raw-filter cover Z is a separate local premise
about supports at live clean transitions. It is independent of T and the
claimed root-cover conclusion. Branching, liveness, and extra-arc premises
are likewise explicit structural properties, not disguised size bounds.

The endpoint is a conditional cover bound of R.card+B.card. It does not yet
identify that budget with the required original-gate partition, prove the
exceptional edge-birth budget, or establish any unrestricted circuit-size
bound. It is not a proof or refutation of the posted gap.
