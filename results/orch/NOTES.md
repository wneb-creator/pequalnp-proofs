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

### lower_bound: certificate reuse and optimization 2026-11-25T19:54:19.769893+00:00
Existing same-gap PR16243 by MohamadEidAlAktaa contains full signed-binary lower13 + monotone witness14, but both remote checks timed out. Source517777bytes7860lines. Static helper pruning initially missed field notation; corrected closure restores CompactTable.live/bucket and BoundPool.wires, leaving48 unused declarations removed. Corrected Pruned.lean494996bytes7573lines.
FastData.lean precomputes all436 rich-domain entries via85 literal128-bit masks; FastDataGraph.lean additionally memoizes graphGoal127 using the existing graph truth word. Core Lean DomainEquality.lean verifies exact129 main-domain equality and the generic fast-graph equality (exit0, kernel1.76s). Full theorem compatibility/runtime still pending. Root notified to preserve compiled optimization certificate and logs.

## replacement_proof optimization update
Original full source profiling has passed17minutes with no Lean errors, kernel phase1168; RSS3.7GiB. Direct rfl leaf proof slower (8nodes27.49s vs decide+kernel11.56s); domain+graph precomputation no clear speedup. Coverage signature compression promising: first512columns pass1255/1256finalnodes, onlyk7i62fails. Lower_bound exact coverage analysis found131selectedcolumns suffice; candidate pending independent screening.

## replacement_proof — 2026-11-25T20:11:54.171258+00:00
FULL ORIGINAL PR16243 source Lean compile exit0,1286.965seconds(21m26.97). Kernel typechecking1240s, elaboration7.89s, imports6.42s; max observedRSS4.14GiB. Complete stdout/stderr/result copied results/orch/lemmas/replacement/full-original.*. This reproduces posted proof and explains prior20minchecker timeout. Signaturecompression still needed for runtime margin. All22gridcomputationalstates dumped11.7MB scratch TSV to support per-grid hitting-set optimization; lower_bound owns that transformation.

## circuit_search width fallback — 2026-11-25T20:14:06.528513+00:00
Generated ParamWidth.lean generic prefix(155013bytes) parameterizes98 width-dependent declarations and8type aliases; preserves semantic Sig128 and Impossible. Added~5.8KB. Optional type-alias defaults allow earlier grids1024 and finalgrid256 without rewriting earlierdata. Prefix compilationFAILED because mechanical named-width applications in simp/unfold argumentlists must revert to bare identifiers; candidate UNVALIDATED. Root selected all-grid Selected256 instead, so fallback refinementstopped. No activeprocess.

### lower_bound: successful sample-column compression 2026-11-25T20:14:15.982824+00:00
Original PR compiles but exceeds20-minute check cap (replacement measured21m27). Analyzed1256mainstates/413377transitions:30955distinct missing-pair masks,101forcedsamplecolumns,30additionaloptimalcovercolumns. Selected131total. Extended to22grids including everyrawprimitive state; earliergrids need6–89columns. Contrary to initialcount, earliergrids could have700distinctpairs; signatureselection preserves required cuts rather than allpairvalues.
Selected256.lean496125bytes7861lines keeps ORIGINALhelperproofs, changes16signaturewidthliterals and44P/Qconstantfunctions only, addsoriginalauthorattribution. Everychosenindex isoriginal0..1023; unusednew256positionsrepeatavalidchosenpair. Mapping selected-pairs.json and fullPythonselectionlog coverage-selection-validation.txt savedhere. Independentcompiledall-node/primitive screening underway withreplacement; rootwillrunfullkernelbuild/checker.

## replacement_proof — selected-column independent screen
Selected256 has passed compiled screening of2655nodes across22grids and82primitive checks withzero failures. Scratch runner initially included8unused augmentedrootnodes through rawcounts; corrected toactualtablecounts, cleanexit0. AllScreenSelected.leanandcomplete logs backedup inresults/orch/lemmas/replacement. Kernel/fullnamedbuild still required.

## Root strategy review

The full original source compiled in 1286.965 seconds and is backed up at commit 7c4adf03. Selected256 preserves every used certificate check in independent compiled screening and passes exact-statement/format review; its named-file build is running. Width reduction alone improved the sampled kernel benchmark by about 11 percent. Direct rfl, whole-node cbv, and simple chartAt cbv staging were not adopted.

Research read 2026-11-25: Lean official tactic reference, https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/: "The proofs produced by cbv only use the three standard axioms." This motivated a standard-tactic experiment; it did not authorize custom code, additional axioms, or extra proof-file options.

### replacement_proof — staged normalization benchmarks

Whole-node `cbv` fails default 100k steps. Staging chartAt using `conv at hs => rhs; cbv` compiles but 8 sample nodes take 7.47 s kernel versus Selected256 baseline 5.76 s. Staged preCov takes 7.8 s kernel; literal chartAt with a checked `decide +kernel` equality improves only to 5.43 s and likely exceeds remaining source space if generalized. Thus no staging variant recommended. All runs use allowed limits only; complete logs under scratch replacement/. No microbenchmark process remains active.

## circuit_search pool ordering — 2026-11-25T20:24:59.286813+00:00
The data-only candidate PoolOrdered256.lean is 496125 bytes and changes 27 existing packed Nat hexadecimal literals. All helper and theorem text is unchanged, and each node retains its original pick multiset. A compiled pool dump (5.4 MB) and Python transition model give 328948 → 309289 pool checks: 19659 saved, or 6%. Final ax127 was already optimal; savings come from 495 earlier-grid nodes. Storage analysis found 2385 unique spans, 89 shared spans, and no partial overlaps; the changes affect 495 unshared spans. Independent compiled screening was requested from replacement. The candidate is NOT kernel-validated. Sources and reports are in the search folder; the full raw pool dump is scratch/all-pools.tsv. No active process.

### lower_bound: width 128 and constructor forcing — 2026-11-25T20:30:59.399553+00:00
Constructor-forcing identities and eight node proofs compile, but measured kernel time 7.56 s versus earlier 5.76 s showed no speedup under concurrent build load. Artifact ForceSamples.lean and validation log preserved; not integrated.
Selected128.lean keeps the original proof and drops only original sample columns 69, 72, 83 from the 131-column main selection. Exactly three branches become newly uncovered; existing pools 59, 75/791, and 72/408 reject them, verified by the existing Python cachedPoolCut port. Earlier selections remain unchanged, all below 128 columns. Source 496068 bytes, 7861 lines. Independent Lean screen pending; Selected256 remains frozen.
Filtering all coverage constraints already rejected by pools reduces the final selection to 113 columns, with 87 forced. Thus this route cannot reach 64 bits without considering links as well. Dropping only three columns should preserve faster coverage pruning than the more aggressive 113-column selection.
