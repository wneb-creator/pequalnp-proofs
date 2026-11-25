# Exact case2 necessary elimination

`Case2NecessaryResultants.lean` is a checked scoped bridge from the six explicit reduced case2 equations to nonzero P, B, curve-leading factor and chart determinant, and to two raw bounded polynomial resultants equal to zero. The field is complex. No slope nonzero assumption or leading-coefficient division is used. The exact original equation mapping and elementary ring reduction certificates were independently reviewed.

The source includes the separately checked generic common-root resultant helper exactly once. Its remaining namespace is `PEqualNP.Outside.L_gct_231_aux.Case2Necessity`. The source compiled successfully in15.31seconds with peak2,795,124KiB. A separate exact-source audit compiled in18.88seconds and reported only propext, Classical.choice, Quot.sound for the five principal theorems. Full logs and metadata are retained.

This does not identify the raw resultants with the divided projective quotient, does not derive the two normalized univariate norm hypotheses in the separate projective-norm certificate, and does not settle GCT-231. Those connecting equalities remain outside this source.

The first failed build lacked noncomputable tags and a recursion limit; the second encountered expensive definitional unification at the final tuple. The final proof uses three scalar ring-normalized goals instead. Exact failed source snapshots are reconstructed and hash-checked against their build metadata, and preserved under failed/.
