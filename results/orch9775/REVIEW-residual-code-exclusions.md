# Independent review: ResidualCodeExclusions

UTC: 2026-11-25T17:45:52.507409+00:00

Verdict: PASS at SHA-256 `cdda0cfe67ff87bd05df353755ce49373ace078733c854e61bb0955d10182aa5` (104 lines, 14,681 bytes). The exact source was checked/exported with empty archived stdout/stderr according to its validation record; no compilation was repeated.

All three theorems retain StrictLive, exact graph computation, Bzero=0, Bplus=11, and an exact ineligible mask. The residual-code dimensions are correctly derived from the surplus/cardinality identity: masks111 and4757 have six ineligible vertices and three residual units; mask2213 has five and two units. The equivalence enumerates the actual residual units, not an arbitrary unrelated family.

I independently parsed every two_exact/exposed_exact mask and vertex parameter from the Lean source and verified the graph geometry, independent sets, ineligibility/eligibility, distinguishing neighbors, exposure witnesses, and shared-neighbor requirements for code_diff. Each derived directed subset constraint agrees with its actual missing-pair witness. code_excludes correctly preserves its empty-code alternative instead of assuming nonemptiness.

The three final universally quantified finite implications were parsed from the source and independently checked over all 4,096, 4,096, and 256 assignments, respectively. No assignment satisfies the stated antecedents. The code variables and h0... argument order match the theorem instantiations. Detailed replay data are in projection/residual-exclusions-independent.json.

No forbidden proof/string/attribute markers were found; options are permitted and locally scoped. CompactFramework is an auxiliary dependency and must be inlined for final submission. This module excludes only the stated three conditional cases.
