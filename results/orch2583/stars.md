# Star construction for L-meta-2583

The checked upper bound is `PEqualNP.Outside.L_meta_2583.Stars.upper` in `lemmas/StarUpper.lean`. It constructs a READ-1 AO2 incidence circuit of size exactly `N * (q + 2) - 1`, stated without truncated subtraction as `D.size + 1 = N * (q + 2)`. Assumptions: `0 < N` and each line has exactly `q+1` incident points. It does not use unique lines through point pairs or the plane cardinality.

Construction: for each line, OR its q+1 point variables using q gates, AND with that line input, then OR all N star outputs using N-1 gates. The proof threads both Boolean values and the exact joint count-vector recursion from ReadK, so READ-1 is witnessed by the pair of distinct point/line unit vectors.

Provenance: this is the self-contained Own construction portion of accepted repository file L_meta_2393.lean, through `upper`, with namespace changed and unrelated portions omitted. Independent reviewer confirmed exact body identity and checked the assumptions; no forbidden constructs were found. The standalone file compiles with only `PEqualNP.Defs`.

`StarReduction.lean` appends `replacement_of_lower_bound` and `posted_of_lower_bound`. These checked implications reduce the desired result internally to the sharp unrestricted monotone lower bound `N*(q+2) ≤ C.size+1`. They are not a submitted reduction, and they do not prove the lower bound.

Relevant existing sharp READ-1 lower bounds: L_meta_7639 gives `E.card + N ≤ C.size + 1` on C4-free bipartite relations containing a perfect matching. L_meta_4897 gives a vertex-cover version. Together with the projective-plane perfect-matching lemma these explain why the star bound is READ-1 optimal; extending that lower bound to unrestricted monotone circuits is the substantive unresolved step.

Validation: StarUpper compiled exit 0, empty stdout/stderr, logs `/tmp/oec/pequalnp-pilot-104/starupper2.stdout` and `.stderr`; StarReduction compiled exit 0 with empty `starreduction.stdout` and `.stderr`. StarUpper frozen SHA256 `70c33f4a7120af93dc238e85d357c2e9b27e2b79e737406b8f0096ec97690ce5`.


The exact converse is now checked. `PlaneCount.read_one_lower` specializes the existing L4897 READ-1 vertex-cover lower bound using the independently checked `PlaneGeometry.lean` component. `Stars.replacement_iff_lower_bound` proves, under the posted plane assumptions, that existence of a no-larger READ-1 replacement for a circuit C is equivalent to `N*(q+2) ≤ C.size+1`. This equivalence does not need C itself to compute the function; its size is the comparison budget. The posted antecedents about C are exactly what must establish this numeric bound.

Preferred integration artifact: `lemmas/StarEquivalencePlain.lean`, all upper/lower/equivalence dependencies in one file with Defs only and all helper declarations inside legal namespaces. The fully qualified cover_bound from original L4897 has been moved inside its ReadLower namespace without changing its name. The original source's linter/deprecation warnings remain, but the file compiles with exit 0 and no errors. Forbidden-token scan found none. Frozen SHA256: `2f43a4b3c1f8491a3c3eae664087a8e67ff83819eb1c04d74d5c80155e1c777f`.

Validation logs: `starlower.stdout/.stderr`, `starequivalence.stdout/.stderr`, `starequivalence-plain.stdout/.stderr` under the task scratch directory; stdout contains inherited warnings, stderr is empty. Root/status_review independently audited StarLower's arithmetic, incidence relation, and retention of READ-1. These are partial results only, with no claim to the unrestricted lower bound.
