# L-meta-2448 independent semantics review

Read 2026-11-25 from GAP_2448.json and current definitions. No Lean verification performed by this reviewer. No counterexample to the posted statement found.

## Statement and small cases

The claim is existential: for every triangle-free, four-cycle-free finite graph, some size-minimal AND/OR circuit for its exact edge function has a star profile. It does not claim every minimal circuit has that profile.

- n=0 is harmless. HasStarProfile explicitly permits each AND gate to own no graph edge; it does not require a vertex witness in that case.
- For any edgeless graph, `{ gates := [], output := n }` computes false, has size zero, is Monotone2, is minimal by natural-number nonnegativity, and has a vacuous star profile. Thus n=0 and n=1 are included.
- The triangle and four-cycle hypotheses are not accidentally inconsistent: irreflexivity excludes loops, and the four-cycle condition permits repeated opposite vertices. Empty graphs, forests and a five-cycle satisfy them.
- Monotone2 means at most two inputs. Nullary AND is true; nullary OR is false; unary gates copy; repeated inputs are permitted. Wiring need not be well formed: nonexistent/future wires and nonexistent output read false. Normal-form arguments must handle these cases explicitly or prove that minimality removes them.
- Owns concerns strict ancestry, not earlier gates globally. An owned pair is one on which the AND gate is true and every AND gate in its strict cone is false. A different earlier AND outside the cone is irrelevant.
- Owns is defined independently of G and also on equal-vertex pairs/nonedges. HasStarProfile filters to actual G edges. Correctness of the output does not imply an internal gate rejects nonedges; later AND gates can filter false positives.
- HasStarProfile quantifies every AND gate, including gates outside the output cone. Such gates can violate the property in nonminimal circuits. Use minimality/replacement; do not infer the profile directly from output correctness alone.

For a triangle-free graph, a nonempty pairwise-intersecting family of graph edges has a common vertex. Start with ab; if not all edges meet a, another edge meets b and misses a. An edge missing b would force a triangle. Thus the substantive normalization target can be phrased as eliminating two disjoint edges owned by one gate.

Sources: lean/PEqualNP/Defs/EdgeOwnership.lean, CircuitLowerBounds.lean, MetaComplexityLgpMono.lean, MetaComplexityMinimal.lean, NestedCoverCircuit.lean. No external mathematical claim is being imported.

## Reported PRs, read-only check

At inspection both PRs were OPEN, unmerged, with empty statusCheckRollup and no issue comments. No acceptance or rejection verdict was present. Full paginated API responses are preserved in /tmp/oec/pequalnp-pilot-74/pr-12430*.json and pr-12779*.json. No comments or other writes were submitted.

- https://github.com/brilliant-hq/pequalnp-proofs/pull/12430: title R_meta_2448_3; adds only R_meta_2448_3.lean, 10 lines. It splits existence of a minimum from a universal claim that every minimal graph circuit has star profile. Its second hypothesis omits the triangle/four-cycle assumptions entirely.
- https://github.com/brilliant-hq/pequalnp-proofs/pull/12779: title L-meta-2448, but its actual diff adds only R_meta_2448_3.lean, 125 lines. It is a reduction, not a completed proof. It uses an existence hypothesis plus a clean-prefix exchange hypothesis on suitably oriented disjoint owned edges.

Neither reported PR supplies a completed proof of the held statement. A later status change remains possible. The desk reports three live reductions already; do not assume either open reduction has room to land or that another reduction is available.

## Flaw in the broad child of PR 12430

This is a counterexample to that PR's stronger hypothesis, NOT to L-meta-2448. Take four vertices and edges 02,03,12,13 (a four-cycle). The three-gate circuit `(x0 OR x1) AND (x2 OR x3)` computes its edge function. Its final AND owns all four edges because its strict cone has only OR gates, so no vertex meets all owned edges.

A complete truth-table signal-set enumeration for at most two gates found no realization. It starts with false and four input truth tables; each gate may produce true, false, a copy, or the AND/OR of two available tables, including repeats. Invalid wires are represented by false. The exhaustive sets at depths 0,1,2 numbered 1,14,140; the target table 61152 was absent at all depths. The displayed three-gate circuit therefore is size-minimal in the model, and its owned-edge family has no common vertex. This finite calculation is not Lean-checked.

Operational conclusion: do not copy the unrestricted every-minimum-star child. Keep graph hypotheses and preserve the weaker existential normalization target.
