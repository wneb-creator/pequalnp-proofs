# Six-case normalization and joint-factor-cost preservation

Research evidence only: the two chain forms plus four AAOA forms have an
independent mathematical and exact-delta PASS. The joint factor inequality
has an independent mathematical PASS and bounded DAG controls. This archive
contains no global refutation, accepted gap proof, or new UNSAT certificate.

The six final cases are AAAA-chain, AAAO-chain, T1, T2, T3, T4. The four AAOA
forms require the absorbed AAAA fallback. These are existence normalizations,
not clauses proved to follow from every model of the original CNF. Preserve
the OR(H,H) to OR(FALSE,H) repair and the prefix prune/pad/re-sort argument.
The weaker encoded AAAA leaf order is safe. See the complete S04 report.

The joint bound requires a minimal family of at least three proper full-cover
factors, productivity, clean prefix ANDs, and a nonempty residual for the
distinguished factor. It excludes both retired 17-prefix triangle families:
N(1),N(4),N(8) requires at least18 gates; N(3),N(6),N(7) requires at least19.
It is not yet a Lean lemma or an implemented cut. The retired triangle
metadata/source is preserved only to identify the hypotheses; S04 did not
complete an independent unit-delta audit of that superseded generator.

## Exact reproduction without raw CNF archival

From any extraction location, with Python3 and a fresh writable OUTPUT:

    python PACKAGE/scratch/orch/S04/reproduce_six_cases.py PACKAGE OUTPUT

No third-party package, solver, Lean, network, credentials, or environment
variables are needed. The recipe verifies all manifest-listed artifact hashes,
uses unchanged archived generators, and builds prefix-base/lex/distinct,
the original DAG parent, all six consecutive-junk-v2 files, and T1-T4.
It verifies all14 CNF hashes and sizes, byte equality of all14 metadata files,
and both family manifests. Output is approximately28MB and is not archived.
The retained reproduction run passed all checks; its full logs and result
are included. Reconstruction files must stay outside this package.

The original parent hash is
38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08.
The full case hashes and dimensions are in the metadata and independent
chain-review.json/aaoa-delta-review.json; manifest.json records every omitted
CNF's exact size/hash and reproduction path. No raw .cnf is included.

## Path and historical-hash resolution

repo/ mirrors /workspace/pequalnp-proofs/; scratch/ mirrors
/tmp/oec/pequalnp-pilot-18/. Original paths inside old logs/manifests describe
the original execution, not the extraction directory. The newly supplied
recipe is portable; historical review scripts remain unmodified evidence.
The old six-case-review-manifest.json binds S04-redteam.md at its earlier
hash a284417b...c42ef. That exact historical report is preserved as
scratch/orch/S04/S04-six-case-reviewed.md. The current report additionally
contains the joint bound review. Existing pending-review fields in generated
metadata are historical generation statuses, superseded by separate S04
reviews, not silently rewritten. NOTES and reports are timestamped snapshots;
other agents may append after this preservation cut.

Early failed control/compile logs are retained beside final successful logs;
only the corresponding final hash-bound results establish their stated
PASS. The S01 Lean Boolean helpers are limited compiled partials already
reported by S01; no new Lean build was performed by this packaging step.
