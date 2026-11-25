# Frozen late research checkpoint

Captured 2026-11-25T12:01:31.441661+00:00. This bundle preserves research for L-gct-231. It contains no complete proof or refutation of the posted statement and no authoritative checker verdict.

## Evidence classes

- Numerical evidence: the 300-start search produced 239 distinct approximate trace-zero planes. Residuals, Jacobians and extension diagnostics are numerical observations; they do not certify exact solutions or completeness.
- Finite-field evidence: the census, direct-permanent audits and S4 orbit classifications apply to the listed finite fields. The orbit code uses push-forward permutations, inverse to Lean's entryPermute pull-back. No characteristic-zero classification follows from these counts.
- Exact algebraic evidence: the valid C3 artifacts give independently audited polynomial identities for nonextension of C3-stable trace-zero two-planes with diagonal rank two. The 24 S4 quartic consequences have exact rational certificates independently checked against raw generators. These computations are not Lean-formalized global theorems.
- Bounded computational systems: both uniform rational and fraction-free exports are retained, together with complete successful, failed and resource-bounded diagnostics. Their elimination results remain inconclusive for the global problem.
- Lean evidence: isolated build logs in this bundle refer to component checks. The checked structural theorem sources are preserved separately, including [AllStarComplete.lean](../../lemmas/AllStarComplete.lean) and [LowDiagonalRankComplete.lean](../../lemmas/LowDiagonalRankComplete.lean). They exclude flats containing nonzero star directions and flats with diagonal-image rank at most one, respectively; they do not settle the posted statement.

## Withdrawn C3 parametrization

The exploratory C3 rational parametrization and its degree-20 output are INVALID and WITHDRAWN because of a cubic-sign error. The files c3_parametrize.py, c3-rational-parametrization.json and c3-parametrize.stdout are excluded. The incomplete c3-power-certificate-trivial.stdout is also excluded. Only the files authorized by c3-valid-evidence-manifest.json appear as C3 evidence. C3-NONEXTENSION.md records the corrected equations and scope.

## Integrity and provenance

Every supplied manifest entry was checked for exact SHA-256 and byte size. The original manifests are retained at their source-relative paths. The required S4 chart dependency is included and checked against its earlier preservation manifest. Independent review reports accompany the applicable evidence.

NOTES.md and TIMELINE.md are unchanged point-in-time snapshots under snapshots/, with their own capture times and hashes in MANIFEST.json. They retain the chronology of abandoned and completed approaches. The correction above applies to the withdrawn C3 parametrization.

All included files were scanned before copying for credential formats, authentication fields, private lease values and credential-bearing URLs. No sensitive values were found. Ordinary recorded renewal events and UTC timestamps were preserved. Full stdout and stderr files are retained.

MANIFEST.json lists all payload files and their evidence classes; it excludes its own hash to avoid self-reference. This directory is frozen. Subsequent work belongs in a new checkpoint.
