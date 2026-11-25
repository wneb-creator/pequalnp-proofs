# Independent search validation audit

Auditor: semantic_audit. Completed 2026-11-25 14:37:33 UTC.

Verdict: PASS for the report's stated experimental scope. No counterexample or unrestricted impossibility theorem was established by these searches. No proof depends on their correctness.

## Independent computations

- Evaluated all 40 embedded 20-gate seeds on all 1,024 inputs: each computes the stated Petersen function. Independently confirmed 76 false rows, minimum vertex-cover size 6, and 5 minimum covers.
- Independently parsed and evaluated every local-search record, including topology and operation-code checks: 12 records from seed 101 and 31 from seed 102, totaling 43. The best no-NOT candidate fails 9 rows; the best containing-NOT candidate fails 10 rows and its sole NOT is outside the output dependency cone.
- Re-decoded the three original partial-row SAT models and evaluated all 1,024 rows. NOT-first, AND-edge-first, and OR-nonedge-first fail 682, 378, and 858 rows respectively. Their decoded NOT counts are 6, 2, and 1.
- Independently checked the six-cycle wrapper identity on all 1,024 inputs. Its proposed 10-gate, four-output core plus 9 wrapper gates would indeed have 19 gates.
- Read complete solver status files and checked timing summaries: fixed-three-OR cores return UNSAT at 6.52s and 10.67s; free-prefix search is UNKNOWN at 300.00s wall time and 238.11s CPU. CEGAR edge and nonedge searches are UNKNOWN at approximately 300s, with the reported row and clause counts.

## Scope and code review

The local C++ truth tables contain exactly 16 words of 64 bits, so every fitness evaluation covers all 1,024 inputs. Both independent validators implement ordinary AND, OR, and one-input NOT, including the appropriate output selection. The SAT validators additionally handle the reference encoding's constant-true operation and false source sentinel. The CEGAR and native incremental drivers check every decoded candidate against the full truth table before reporting a functional match.

The hexagon CNF's operation/source one-hot constraints, gate truth clauses, 64 output rows, three exposed pair-OR constraints, NOT limits, and source ordering agree with the reported restricted construction. Its UNSAT result is not claimed to exclude arbitrary Petersen circuits. The broader free-prefix search timed out.

The full Petersen searches fix a first gate and impose reference normal forms; with the fixed nonpadding first gate, the reference prefix-padding clauses leave exactly 19 nonpadding gates. There is no complete proof here that all smaller circuits with at least one NOT normalize into these cases while preserving that requirement. UNKNOWN results establish no exclusion in any event. The uncertain shared OR-nonedge log is explicitly omitted from claimed results.

A nonblocking future robustness issue: `search_local.cpp` terminates at zero truth-table errors even if a candidate has no NOT. Any future zero-error hit must also satisfy the posted at-least-one-NOT requirement. `search_validate.py` records both total and live NOT counts, allowing this check. The present report correctly claims no witness.

Selected sources, report, and full local-search logs contain no credential-shaped values; the search code makes no credential-store reads, environment dumps, or network requests. The audit did not access environment credentials.

Full audit stdout/stderr is preserved as `logs/semantic-search-audit.log`. This audit covers the following source snapshots only; later experiments require separate validation.

- `1fdbd15923f72cb7d549d710f2d0e94295edb21386aec0468228c5be5308096a` `results/orch/COUNTEREXAMPLE_SEARCH.md`
- `dbdbfed260c4e2775be93b871b68b6a916d053aadf543167be1d5f5edfede114` `results/orch/lemmas/search_local.cpp`
- `927d3b7ef54df4431824fa35cb3dd1eac7e723bb187157fec6d44f868d94fbcd` `results/orch/lemmas/search_seeds.hpp`
- `59d5b8f27d85341aeeb02065f0f84ca36271356d08b77641b3913f85da947be1` `results/orch/lemmas/search_validate.py`
- `30dc2c50b4ba1f77e18979bfb15134285b5013438d6678654cdc9c8bc254d9af` `results/orch/lemmas/search_hexagon.py`
- `76a9fb03bd9cd00deb4af5c070ac00945cc1e66d03c202e4ed7418858220d43f` `results/orch/lemmas/sat_cegar.py`
- `0bb88df90a268637b3770a02135aa14c78fab5b4f2e04c097d68cfac9b4f2654` `results/orch/lemmas/sat_incremental.cpp`
- `26fcc3fff9bab6324c429f026844fb44255791bf314052561b4236c01bbbcfda` `results/orch/lemmas/sat_validate.py`
