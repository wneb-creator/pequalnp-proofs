# Independent review for L-meta-2583

Reviewer: semantics agent. Reviewed 2026-11-25 UTC.

## existing_star_builder.lean

SHA256: `55fdd3e3c445956ee0c82037e48eb6e9b9359820f6ed5d35b171ed595acd1b95`

Verdict: PASS as a checked partial helper; not a complete proof of the posted statement.

The builder assigns each incidence edge to one selected endpoint, makes a star for each nonempty assigned set, and joins star outputs by binary OR gates. Its `Good` invariant enforces AND/OR gates only, exactly two operands, backward reads, and disjoint input-side types for the operands of every AND. The construction counts one gate per assigned edge and one top OR per additional nonempty star. The read-vector induction establishes one jointly bounded vector, rather than separate per-variable minima: the two AND operands provide distinct unit vectors because they belong to opposite input sides. Thus `starCover`, `lineStarUpper`, and `normalize_of_budget` have the stated semantics.

Caveats:

- `normalize_of_budget` explicitly assumes the remaining hard lower bound `N * (q + 2) - 1 ≤ C.size`. It does not establish that bound or the original gap.
- The generic empty-edge case uses a missing output wire as the constant false function. This is permitted by `IsAO2`, which constrains gates but not output validity. It cannot occur for the posted projective-plane hypotheses; `plane_output_gate` in the separate semantics helper proves that fact.
- The compilation log contains only inherited unused-tactic and deprecation warnings. I inspected the complete source and the author's complete logs; I did not rerun a redundant build.

## lower_singleton_star.lean

SHA256: `e0dc893c1dec5854ab2d2d3a154d7f6ad2b75dd4f53448add31aa95dfedf8c08`

Verdict: PASS as a checked partial helper; not a complete proof of the posted statement.

`singletonTrace` records singleton inputs accepted by a monotone factor. If the conjunction of two factors implies the graph edge function, monotonicity makes each cross pair of singleton traces an actual graph edge. Looplessness gives disjointness, and the exact `NoFourCycle` definition bounds one trace by one vertex. These statements correctly use full-input semantic cleanliness, not just acceptance on edges.

Caveats:

- The conclusion controls singleton traces only. It does not show that every accepted edge comes from a singleton on each side. A repeated proof tree can use a factor which accepts the pair while accepting neither endpoint alone. Any global normalization using this lemma must separately handle those edges.
- The compilation log has three cosmetic `simpa` warnings only. I inspected the entire source and complete log; I did not rerun a redundant build.

## Format audit

Both files import only Mathlib modules and `PEqualNP.Defs`. Every declaration is inside `PEqualNP.Outside.L_meta_2583_aux` or a nested namespace. No forbidden proof escape, axiom declaration, string literal, forbidden attribute or option, custom inductive declaration, or prohibited root-name text occurs. A bounded forbidden-pattern scan returned exit 1, meaning no matches. Hashes were checked again after the source review and were unchanged.

These are preserved research helpers. Neither file is independently suitable as the final single proof file: final submission still needs the exact full-name theorem for the posted gap, outside the helper namespace and last in the file, and the remaining proof obligation must be discharged.
