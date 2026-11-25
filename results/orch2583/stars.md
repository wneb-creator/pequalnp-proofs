# Star construction for L-meta-2583

The checked upper bound is `PEqualNP.Outside.L_meta_2583.Stars.upper` in `lemmas/StarUpper.lean`. It constructs a READ-1 AO2 incidence circuit of size exactly `N * (q + 2) - 1`, stated without truncated subtraction as `D.size + 1 = N * (q + 2)`. Assumptions: `0 < N` and each line has exactly `q+1` incident points. It does not use unique lines through point pairs or the plane cardinality.

Construction: for each line, OR its q+1 point variables using q gates, AND with that line input, then OR all N star outputs using N-1 gates. The proof threads both Boolean values and the exact joint count-vector recursion from ReadK, so READ-1 is witnessed by the pair of distinct point/line unit vectors.

Provenance: this is the self-contained Own construction portion of accepted repository file L_meta_2393.lean, through `upper`, with namespace changed and unrelated portions omitted. Independent reviewer confirmed exact body identity and checked the assumptions; no forbidden constructs were found. The standalone file compiles with only `PEqualNP.Defs`.

`StarReduction.lean` appends `replacement_of_lower_bound` and `posted_of_lower_bound`. These checked implications reduce the desired result internally to the sharp unrestricted monotone lower bound `N*(q+2) ≤ C.size+1`. They are not a submitted reduction, and they do not prove the lower bound.

Relevant existing sharp READ-1 lower bounds: L_meta_7639 gives `E.card + N ≤ C.size + 1` on C4-free bipartite relations containing a perfect matching. L_meta_4897 gives a vertex-cover version. Together with the projective-plane perfect-matching lemma these explain why the star bound is READ-1 optimal; extending that lower bound to unrestricted monotone circuits is the substantive unresolved step.

Validation: StarUpper compiled exit 0, empty stdout/stderr, logs `/tmp/oec/pequalnp-pilot-104/starupper2.stdout` and `.stderr`; StarReduction compiled exit 0 with empty `starreduction.stdout` and `.stderr`. StarUpper frozen SHA256 `70c33f4a7120af93dc238e85d357c2e9b27e2b79e737406b8f0096ec97690ce5`.
