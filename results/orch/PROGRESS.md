# L-gct-231 final partial-result handoff

Updated 2026-11-25T13:20:30.810320+00:00. Work is stopped because no fresh own lease was obtained. This branch contains checked partial results; it does **not** prove or refute the posted statement and has no required final declaration, proof PR or authoritative checker verdict.

The question is whether a three-dimensional complex linear subspace of symmetric four-by-four matrices can satisfy `permanent(J + T) = 24` for every member, with every entry of `J` equal to one. A complete negative answer must be packaged as the exact posted negated twin, L-gct-232, and pass the repository's ordinary checker.

## Terminal desk outcome

Work stopped after the owned L-gct-231 lease returned HTTP410. The complete response and advertised-expiry discrepancy are preserved in [desk-410-response.txt](desk-410-response.txt) and [desk-410-status.json](desk-410-status.json). The coordinator pushed the immutable work at `add965fc` before making the two permitted reacquisition attempts. Both returned the same other pilot's lease with the exact note:

> you hold 5 gaps, the most one handle may hold at once; release one to get another

No fresh own lease was obtained. No other pilot's lease was renewed, released or worked. The old own lease was already invalid, so there was no live own lease to release. Both remaining native processes were terminated; their final records are in [final-termination-checkpoint](research/final-termination-checkpoint/MANIFEST.json). Neither produced a completed basis or certificate. No further mathematics or builds were run after the freeze.

There were **20 original null desk answers** before the initial successful lease. The last generic null answer was exactly:

> No step is free right now. Please do not pick one from the public file: it may already be held, and only the first valid proof of a step is recorded. Ask again in a few minutes.

All 20 exact texts, including the earlier cooldown variants, and both terminal attempts' shared-handle outcome are recorded in [terminal-desk-status.json](terminal-desk-status.json). The task ends with preserved checked partial results, **no full proof/refutation, no PR and no authoritative checker verdict**.

## Current checked source

`lean/PEqualNP/Outside/L_gct_231.lean` has **3700 lines and 211 unique declarations**, all helpers in `PEqualNP.Outside.L_gct_231`. Its SHA-256 is `b55fd4b239beee330a11821866d1be204f7c405502eddf617c02d1f13bc5c30e`. The latest `lake build PEqualNP.Outside.L_gct_231` exited 0 and reported `Build completed successfully (5159 jobs).` Complete logs are `combined3700-build.stdout`, `combined3700-build.stderr`, and `combined3700-build.exit`; exact hashes are recorded in `validation.txt`. Independent integration/source/format review passed.

The main file includes the following complete restricted results:

- `star_two_dimensional` constructs a two-dimensional example with upper-triangular entries `(T01,T02,T03) = (a,b,-a-b)`.
- `hollow_flat_finrank_le_two` bounds every valid hollow subspace by dimension two. Hollow means every diagonal entry is zero.
- `containing_nonzero_starMatrix_finrank_le_two` bounds any valid subspace containing a nonzero star direction by dimension two, including all basic and exceptional parameter cases. Coordinate permutations preserve the result.
- `level_flat_constant_diagonal_zero` proves that a valid direction with constant diagonal has zero diagonal.
- Triangle projection coverage, normalized Witt coordinates, a seventeen-case algebraic chart classification, exact coordinate permutations and canonical-plane maximality establish `valid_flat_containing_hollow_two_plane`: a valid subspace containing a hollow subspace of dimension at least two has dimension at most two.
- `valid_flat_diagonal_rank_le_one` consequently excludes a three-dimensional valid subspace whose diagonal-image rank is at most one.

A hypothetical three-dimensional example therefore has diagonal-image rank two or three. The new route bridges reduce these cases to explicit arithmetic obligations; neither obligation has been discharged.

## Diagonal rank two: one explicit missing arithmetic premise

The main file proves that a dimension-three, diagonal-rank-two valid subspace contains a nonzero hollow direction and a nonhollow trace-zero direction. It normalizes these directions, transports the incident condition under permutations, and proves that vanishing of all opposite-edge products forces a permuted nonzero star. Its theorem `no_rank_two_diagonal_three_flat_of_normalized_incident` is explicitly conditional on `NormalizedIncidentOppositeEdge`.

The main file also contains the exact twelve normalized incident generator definitions and the checked theorem `normalized_incident_generators_zero` deriving their vanishing from the permanent identity. Independent direct-permutation and symbolic audits agree with these definitions.

The separately checked **48-line** `lemmas/IncidentArithmeticGlue.lean` defines `NormalizedIncidentArithmetic` and proves `normalized_incident_of_arithmetic`. The premise says that the twelve generator equations and the inverse guard

`zz * (-1 - x3 - x5 - x7 - x9) - 1 = 0`

are inconsistent over the complex numbers. The guarded expression is the normalized opposite edge. Proving this premise unconditionally would close the entire diagonal-rank-two case through already checked geometric steps. **No rational inconsistency certificate has yet been recovered.** A finite-prime unit candidate and bounded/interrupted recovery attempts are evidence for further work, not a proof of the premise.

## Diagonal rank three: checked coordinates and radial formula

The main file proves exact Hadamard-coordinate reconstruction, injectivity/bijectivity of the three diagonal-difference coordinates on a hypothetical rank-three flat, and the normalized trace-zero incidence family. These parameterizations have no unproved arithmetic assumptions.

The separately checked **162-line** `lemmas/CanonicalHomogeneous.lean` additionally proves the canonical family with `D = (s,t,u)` and row-major coefficient matrices `P` and `B`. Its exact radial permanent formula has a quadratic term `q`, cubic term `c/2`, and quartic term `p/32`; the three homogeneous polynomials have 9, 36, and 123 terms. The permanent identity forces all three to vanish on the family. This component passed Lean and independent arithmetic/source review; it establishes necessary equations, not infeasibility.

The **31-coefficient collection bridge is drafted and independently audited but has not yet compiled**. Its generator definitions match the authoritative eighteen-variable chart exactly, and its finite-difference identities have independent exact checks. A 174-line equivalent normalization was independently audited, but its controlled check aborted at the managed-memory limit and produced no olean. A reduced 217-line scalar prelude, 1296-line coefficient collection and 24 extra-quartic consequence drafts are preserved with exact source audits; they remain uncompiled. All further checks stopped when the invalid lease was detected.

The missing rank-three obligation is an exact complex inconsistency proof for the 31 canonical coefficient equations, or a verified reduction from an equivalent augmented system. The 55-equation native chart adds 24 independently audited rational quartic consequences. No completed exact inconsistency certificate or global nonextension theorem is claimed.

## Research evidence and limitations

The frozen directories under `research/` preserve exact restricted algebraic certificates, independently audited necessary equations, finite-field censuses, numerical candidates and complete bounded-search diagnostics. Each checkpoint states its own scope and hashes. Restricted B-rank-zero and certain B-rank-one exclusions are exact algebra outside Lean; they do not settle the full rank-three case. Negative bounded modular searches establish neither characteristic-zero nonexistence nor existence. A deliberately stopped Singular process can return exit 0 through its signal handler; the termination/status records control interpretation.

The auxiliary shortcut that every complex trace-zero valid two-plane is hollow is false. An exact degree-sixteen algebraic construction produces nonhollow examples containing a basic star direction, with independent permanent-residue verification. It is not a counterexample to the posted three-dimensional claim. The withdrawn C3 degree20 parametrization remains excluded, and the shifted-filtration claim is corrected by the preserved `SHIFTED-FILTRATION-ERRATUM.txt`.

## Verification and preservation

The named 3700-line main build and the standalone 48/162-line components passed. The 31-coefficient bridge and optimized 174-line version are uncompiled drafts. A separate five-theorem axiom audit of the earlier 2629-line main snapshot found only `propext`, `Classical.choice`, and `Quot.sound`; it is not an audit of every current declaration and is not a repository-checker verdict.

The full checker has no verdict. Earlier unchanged-checker smoke runs stopped under container memory/disk pressure, and the full runtime has not been retested after cache migration. The posted final theorem is absent, so successful helper builds cannot constitute acceptance. Checker code and project build configuration were not altered.

Research and logs are preserved on the task branch under the push-early instruction. A future proof PR must have a final diff adding exactly one correctly named Lean file; branch-only research must be absent from that PR diff while remaining preserved in history. `NOTES.md` and `TIMELINE.md` retain intermediate and abandoned routes; use successful logs and the explicit scope statements here for current conclusions.

Sub-agents: construct_search, geometry_search, status_review, toolchain_setup, artifact_analysis, rowzero, net_normal_form
TIMING total=305.7 subagents=7
