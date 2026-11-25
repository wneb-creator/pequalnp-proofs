# Integrated31 source-preservation and format review

Reviewer: global_normal_form, 2026-11-25 UTC. Verdict: PASS for integration
correspondence and helper-file format. Compilation is separately managed by
the root worker; no duplicate build was run here.

Candidate: `Integrated31.lean`, 1,527 lines and 101,073 bytes, SHA256
`3989f440a6778c2203de025027bf6dd77af6d91a10b1183e32274db49d7fa3b9`.

The existing 624-line named source at SHA256
`ad7a60b2d369921dde6ee77592c01d528e6e22dbcc22fc9b063d37fa6dc03572`
has its entire namespace body preserved byte for byte as the candidate's
prefix. Thus all existing theorem statements, definitions, and proofs are
unchanged. Only the import list is narrowed.

The appended body comes from the reviewed 916-line coefficient source at
SHA256 `d7bf606daad095450d7e07956c199a4c53a96aab17ad1d3f93196c405f3fe351`.
Its only removed declarations are `starAffine` and `fullStarMatrix`; each is
byte-identical to its existing definition. Apart from one additional blank
separator line, the remaining appended text is exact. All thirty-one
individual coefficient theorem bodies remain unchanged.

The combined 200 declarations are precisely the union of the two source
declaration sets with those two duplicates removed. None is renamed,
shadowed, or added outside that set. The source has one auxiliary gap
namespace and no fabricated posted theorem; it remains partial helper work.

The eight specific Mathlib imports precede PEqualNP.Defs and all body text.
No later import word occurs. Every option is a correctly scoped numeric
maxHeartbeats or maxRecDepth limit, both allowed by CONTRIBUTING.md. No
admission, added axiom, native_decide, root marker, double quote, attribute,
custom instance, datatype, executable command, or unsafe declaration was
found. The candidate is below the 512-KiB limit.

The first review attempt required exact blank-line identity and detected
the extra separator. `append-diff.txt` shows that sole whitespace delta;
the corrected comparison checks exact nonblank content and passes. Full
diagnostics are retained in `check.log` and `check-v2.log`, with the
independent checker in `check.py`.
