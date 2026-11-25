# L-gct-231 research checkpoint

This branch does **not** yet prove or refute the posted statement. No proof PR has been opened. The named Lean file contains checked helper theorems, not the required final declaration.

The question is whether a three-dimensional complex linear subspace of symmetric four-by-four matrices can satisfy `permanent(J + T) = 24` for every member, where every entry of `J` is one. A full negative answer must use the site's posted negated twin, L-gct-232, with its exact statement and ordinary checker mode.

## Checked mathematical results

The source is `lean/PEqualNP/Outside/L_gct_231.lean`. All helper declarations are in `PEqualNP.Outside.L_gct_231`.

- `star_two_dimensional` constructs a two-dimensional example. Its nonzero upper-triangular entries are `(T01,T02,T03) = (a,b,-a-b)`.
- `hollow_flat_finrank_le_two` bounds every valid hollow subspace by dimension two. Here hollow means that every diagonal entry is zero.
- `containing_generic_star_line_finrank_le_two` excludes a three-dimensional space containing a generic star direction; its nonzero-parameter hypotheses matter.
- `level_flat_constant_diagonal_zero` says that a valid direction whose diagonal entries are all the same scalar has that scalar zero.
- The three canonical hollow planes have checked maximality results. The other two families have upper-triangular edge coordinates `(a,a,-2a,0,b,-b)` and `(a,b,-a-b,a-b,-2a-b,a+2b)`, in edge order `(01,02,03,12,13,23)`.
- Triangle projection coverage, normalized coordinates, a seventeen-case algebraic chart classification, and exact coordinate permutations give a classification sufficient for the complete lower-rank result below.

The independently reviewed standalone component `lemmas/LowDiagonalRankComplete.lean` compiled successfully and proves:

1. `valid_flat_containing_hollow_two_plane`: if a valid symmetric subspace contains a hollow subspace of dimension at least two, its dimension is at most two.
2. `valid_flat_diagonal_rank_le_one`: if the image of the diagonal-entry map has dimension at most one, the valid subspace has dimension at most two.

Thus a hypothetical three-dimensional example must have diagonal-image dimension two or three. These cases remain open. The complete component includes its preceding coordinate and orbit lemmas and imports the earlier named-file checkpoint; it should not be appended a second time after it has been integrated.

## Exact calculations outside Lean

`research/family-checkpoint/family-preservation.zip` contains exact certificates, verifiers, complete diagnostics, and scope notes for the bipartite and two canonical nonstar hollow-direction families. These calculations exclude restricted parts of the diagonal-rank-two case. They are not Lean proofs and do not cover the generic hollow-direction surface.

`research/s4-checkpoint/` contains the rational eighteen-variable chart for diagonal-rank-three candidates, its independent equation and symmetry audits, and modular certificate searches through degree eight. Each unsuccessful bounded search has a verified modular dual. Those duals establish only failure of that bounded modular certificate search. They establish neither characteristic-zero nonexistence nor existence. The numerical searches found no solution and provide no proof.

The active alternative is to classify valid trace-zero two-dimensional spaces and exclude their extensions. The stronger shortcut that every such complex space is hollow is false: an exact degree-sixteen algebraic construction gives nonhollow examples containing a basic star direction. Its equations and independent permanent-residue verification are preserved separately; this auxiliary construction is not a counterexample to the posted three-dimensional claim. Small finite-field censuses also have nonhollow planes. Neither a finite-field example nor its absence settles the complex classification.

## Verification and preservation

Complete successful build output and independent review records are stored alongside `validation.txt`. The repository's full checker has no verdict: its runtime smoke was blocked by this container's memory/disk limits, and the posted theorem is still absent. The checker and project build configuration were not altered.

Research and logs are preserved on the task branch under the user's push-early instruction. A future proof PR must have a final diff adding exactly one correctly named Lean file; these branch-only research files must be absent from that PR diff. Preserve them in branch history when preparing such a clean tip.

`NOTES.md` contains the detailed parallel research record; `TIMELINE.md` records timestamps. Some notes describe abandoned or incomplete routes. Prefer exact successful logs and the explicit scope statements here over an intermediate hypothesis.
