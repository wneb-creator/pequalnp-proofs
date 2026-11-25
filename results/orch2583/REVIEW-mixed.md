# Independent review of MixedSets.lean

Reviewed UTC: 2026-11-25T14:55:24.843118+00:00
Reviewer: status_check; author: partial_lean. Reviewer did not author or modify this proof.
Input: results/orch2583/lemmas/MixedSets.lean
SHA256:913df22a6d76076fa5651015ac47f471acc48b97edc9d39ccfcb9b6b0801742d
Size:11,788bytes;260lines.

Verdict: PASS semantic and source-format review for a partial checkpoint, subject to the planned assembled-file build after changing imports.

Exact scope and proof:

- `lines_have_at_most_one_common_point`: two common points would violate the uniqueness of their joining line. It assumes only the point-pair unique-line axiom and distinct lines.
- `dual_unique_point_of_degrees`: positive equal row/column degree plus unique point-pair joins imply distinct lines meet in exactlyone point. If l,l' were disjoint, choosing p on l' injects the d points of l into the d−1 lines through p other than l'. The injectivity and exclusion arguments use the correct distinctness hypotheses. No unstated projective-plane duality is assumed.
- `nonincident_mixed_sets_bound_of_degrees`: with both degrees q+1 and q>0, nonempty pointset A and lineset B containing no incidence obey |A|+|B|≤N−q. For p0∈A and l0∈B, remove p0 and let R be lines outside the q+1 lines through p0 and B. Every other A-point has exactlyq neighbors in R. Every R-line has at mostq A-points because its intersection with l0 lies outside A. Double counting cancels positive q and gives the result. Both nonemptiness assumptions are necessary to this proof and explicitly present.
- `point_degree`: derives row degree q+1 from exactly the posted plane assumptions by partitioning all points other than p among lines through p; q>0 follows from q≥2. No row regularity is smuggled into this wrapper.
- `nonincident_mixed_sets_bound`: supplies derived point degree to the general lemma.
- `mixed_vertex_cover_bound`: if both S and T are proper subsets and together cover every incidence, their nonempty complements are nonincident, giving |S|+|T|≥N+q. The hypotheses are precisely both sides proper, not merely that both sides are nonempty. Full single-side covers of sizeN are therefore correctly excluded. Natural-number subtraction is handled using positivity of the complement, with no missing N≥q premise.

All declarations lie in PEqualNP.Outside.L_meta_2583.Geometry. No sorry, axioms, native_decide, forbidden identifier text, string literals, attributes, or option commands occur. The standalone source uses three Mathlib import lines and no Defs import. Parent plans to replace those with the single allowed `import PEqualNP.Defs` when inserting the complete namespace body; transitive import availability must be established by the assembled build. Replacing the old Geometry section avoids duplicate declarations. The Deletion namespace is separate and does not collide.

Compilation evidence: root reports standalone compilation passed. `2583-mixed-third.stdout` contains only two unnecessarySimpa linter warnings (lines239and246); stderr is empty. Reviewer did not rerun the compiler. This file proves geometry helpers only and does not claim the posted circuit-replacement theorem. A final proof PR remains inappropriate until the exact target theorem is proved and checked.

## Superseding review: CoverClassification.lean

Reviewed UTC: 2026-11-25T14:55:46.637162+00:00
Input: results/orch2583/lemmas/CoverClassification.lean
SHA256:259ac20a01378faa32414842efc6704b98accd3d4f61c39601e6761107920de3
Size:13,419bytes;298lines.

Verdict: PASS. This supersedes the MixedSets-only input for the planned assembled checkpoint. A complete text diff confirms all previously reviewed MixedSets content is unchanged; exactly38lines add two lemmas before the existing namespace end. Forbidden-form checks were rerun on the full superset and remain clear.

`vertex_cover_bound` proves every plane incidence cover S∪T has size at leastN. If either side is all vertices this is immediate; otherwise the already-reviewed mixed cover bound gives the strongerN+q.

`minimum_vertex_cover_pure` assumes an actual cover and the exact cardinality |S|+|T|=N, then proves it is either all points and no lines or no points and all lines. The full-side cases force the other side empty by cardinality; the proper-side case contradictsN+q≤N withq≥2. There is no missing assumption that the cover is inclusion-minimal or that a minimum exists: the theorem uses the exact sizeN hypothesis directly.

Root reports successful standalone compile; `2583-cover-first.stdout` contains only the same two inherited unnecessarySimpa warnings, stderr empty. Replacement of the standalone Mathlib imports by Defs and integration with Deletion still require the parent’s assembled-file build. No final circuit-replacement theorem is claimed.
