# Pilot 184: L-meta-10760

Root alone owns the desk lease and git writes. Final PR must add exactly the named Lean file; progress records will be retained in branch history and removed from the final diff.

## Statement

Seven-input graph with edges 02, 13, 04, 14, 24, 05, 15, 35, 06, 26, 36, 56. Show every AND/OR/NOT circuit with fan-in at most two and at most one NOT has an AND/OR circuit no longer. Exact statement is in `/tmp/oec/pequalnp-pilot-184/desk-001.json`. Reductions are not open.

## Shared findings

- Updated CONTRIBUTING requires helper declarations in `PEqualNP.Outside.L_meta_10760` or its `_aux` namespace. Final fully qualified theorem is last, outside that namespace.
- No same graph found in current checked proofs by initial scans.
- Nearby proofs use explicit monotone upper bounds plus certified signed-binary lower bounds, counting a NOT as one extra gate.
- Toolchain and warm cache promised by kit are absent; setup agent is installing Lean selectively within 6.3 GiB free space.

## Replacement strategy

Owned by replacement_proof.

## Lower-bound strategy

Owned by lower_bound.

## Circuit search

Owned by circuit_search.

## Independent review

Owned by status_review.

## lower_bound — 2026-11-25T19:38:14.869680+00:00
Checked 1549 files numbered 10xxx–12xxx: no isomorphic seven-vertex twelve-edge target. Degree sequence [4,3,3,3,3,4,4]. Nearby L_meta_10772 contains generic SignedBuild, double_cut, cut_signed theory (1362 lines); L_meta_10752 has ForestCore certified lower-bound search (4400 lines). Allowed Defs import means copy relevant helper declarations into final namespace instead of importing those files.
Recursive essential-variable restriction bound with triangle=4 and K4=7 signed-binary bases reaches only 9; all false cofactors bound8, degree3 true cofactors7, degree4 true cofactors5. Thus this alone is insufficient for current monotone upper14. Exact existing same-gap PR#16243 source is being fetched by status_review; await it before recreating large certificate machinery. Scratch tree: /tmp/oec/pequalnp-pilot-184/lower-bound/restriction-bounds.txt.

## circuit_search — 2026-11-25T19:38:32.438014+00:00
Simple formula upper14: OR of (x0∨x2∨x3∨x5)∧x6, x3∧(x1∨x5), (x0∨x1)∧(x4∨x5), x2∧(x0∨x4). Exhaustive search of all66 bicliques with shared OR subsets still gives14 (78,745 states visited). Exact target list and isomorphic target absent from915 Fin7 Outside files. C++ stochastic general-circuit13 search running; SAT mono13 CNF ready with boundary rows and symmetry. Root owns lease.

## circuit_search update — 2026-11-25T19:39:32.386384+00:00
Root located exact prior PR#16243 with14-gate witness and signed-binary lower13, matching restricted search optimum. The graph has independence number2: target false only on empty/singleton assignments and9 nonedge pairs; monotone boundary therefore21 rows (12 true edges plus9 false nonedges). genmono.py can use rows,inc,lex for a small38,304-clause13-gate synthesis instance. Stochastic search currently best2 truth-table discrepancies, no13 witness.

## replacement_proof — 2026-11-25T19:40:08.784536+00:00
Initial scan1185 one-NOT proofs found no isomorphic target; exact-edge scan no checked file. Existing L_meta_10770 technique counts binary gates with free negations then pays one for any NOT. SAT→Lean tools in notes/data/lrat-link: gennot.py, genmono.py, genrow.py. Inlining Checker+LinkN+LinkN2+Shannon costs114KB but custom Trie/model structures need manual review or replacement; BinaryTree (Option Nat) is drop-in for Trie. Official CaDiCaL building in scratch. Primary route now profiling existing same-gap PR#16243 (twice timeout): frozen lower-bound/Pruned.lean494450bytes. Root initial cache/build pending; replacement owns --profile baseline, lower_bound owns explicit table/pool optimization.

## circuit_search SAT result — 2026-11-25T19:49:19.517582+00:00
CaDiCaL monotone13 on boundary21 rows,38,304clauses hit its180s wall limit with exit0/no SAT-or-UNSAT verdict.2,075,720conflicts;34.36MB resident. No13-gate witness. Full logs saved in results/orch/lemmas/search/. Exploratory route finished; root prior-PR certificate route remains primary.
