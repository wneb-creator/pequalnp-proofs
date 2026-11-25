# Orchestration notes: L-meta-2625

The desk assigned this step as a reduction-only task. The posted goal asks for a monotone circuit with at most 63 gates, correct on incident pairs and the specified generic negative inputs of the order-3 projective plane.

## Status

The reduction `R_meta_2625_50.lean` builds and passes the local checker in reduce mode. Cleanup shortened it from 60 to 58 lines; build, format guard, and checker passed again. It has two independent hypotheses: a 30-gate assembly theorem and a 33-gate search on a 20-input residual. The residual existence hypothesis remains open.

The selected seven points are the union of lines 0 and 1: `{0,1,2,3,4,9,10}`. They give 28 required incidence pairs. Six omitted point stars use 29 gates; one final OR gives the assembly overhead of 30. The residual is a subdivided K3,3 with two line hubs and their common point.

## Independent finite checks

- The parameterized negative inputs give 624 rows and 468 distinct inputs.
- The maximal permissible monotone envelope has 52 incidence terms, 52 collinear point triples, and 52 concurrent line triples. It has 12,234 false inputs and precisely the 468 posted maximal negative inputs.
- The selected residual has 102 maximal false inputs for its exact edge function; 66 are absent from the projected generic constraints. It retains eight collinear point triples.
- Independently removing dominated projected constraints leaves 243 negative samples.
- A concrete 34-gate residual and 64-gate completion pass all 28/52 positive pairs and all 624 parameterized negative rows. This is a sanity baseline, not a 33/63-gate witness.
- A smaller 17-input residual was considered but not selected: it imposes a stronger localization assumption and removes potentially useful triples.

## Strategies and review

Six sub-agents handled rules/toolchain setup, reduction design, circuit construction searches, finite checks, independent mathematical review, and a constructive assembly proof. The geometric prime-implicant route was dropped after a complete 22-page open-PR census found the same approach in PR #8889. The chosen two-line residual is distinct from that route and the two existing reductions.

Independent review confirmed the exact posted conclusion, format rules, independent hypotheses, gate arithmetic, and absence of false-positive boundary edges. It did not prove the residual existence conjecture. The exact assembly hypothesis now compiles in `lemmas/Compiler.lean` (234 lines). The standard 34-gate residual also compiles in `lemmas/Core34.lean` (61 lines). These checked auxiliary results are preserved in branch history; the 33-gate core remains open.

## Environment and preservation

The promised Lean installation and cache were absent. Official Lean 4.36.0 and all 9,117 Mathlib cache artifacts were installed under scratch without changing pinned project configuration. Full build/checker logs are retained here. Research artifacts are preserved in branch history and removed from the final PR tree so the PR adds exactly one Lean file.

L-meta-1035 is not open according to the desk: it was checked or stood down. No lease belonging to another pilot was used or released. No null desk assignment was received.
