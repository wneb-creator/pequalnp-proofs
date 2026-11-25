# L-meta-670 orchestration

Lease acquired 2026-11-25 03:00:15 UTC. Only root handles desk, git commits and pushes.

Goal: exact posted 9-input Petersen-minus-vertex 15-gate lower bound, imports PEqualNP.Defs plus Mathlib only. Three reductions already live. Append dated findings here, and keep candidate Lean under results/orch/lemmas or job scratch.

2026-11-25T03:01:49.272223+00:00

## Inventory (status_review)
- Current upstream has first-gate cases NOT0 L1665, NOT4 L1666; AND reps L1667–1672 (01,02,03,04,06,46); OR reps L1673/1674/1676/1677/1678 (01,02,04,06,46). Original OR03 L1675 absent.
- L4734 packages all six AND reps using only PEqualNP.Defs, 381605 bytes. L1680 proves removal of a constant/copy gate, 28807 bytes. Individual case files are 200–518KB, so naive inlining will exceed final 512KiB limit; shared certificate machinery likely needs deduplication.
- GitHub canonical repo is open-goat/pequalnp-proofs. Complete search census for L-meta-670: 11 matches, actual L670 proof PRs all closed; R670719 PR11232 is open although desk says three reductions live.
- Public sketch path https://pequalnp.com/routes/lgp/own/filing/petersen/SKETCH.md inaccessible via web tool; not assuming contents beyond desk sketch.
- Detailed theorem inventory saved in /tmp/oec/pequalnp-pilot-61/petersen-theorem-inventory.txt; candidate list likewise petersen-candidate-files.txt. Search for newer OR03 and normalization ongoing.

## 2026-11-25T03:03:57.199407+00:00 — normalization agent

- Re-derived graph automorphism group by enumerating degree-preserving permutations: exactly 12.
- Kernel-checked 53-line `results/orch/lemmas/Normalization.lean`: explicit table, bijectivity, exact edge function invariance, vertex reps 0/4 and six pair reps. Build exit 0, empty diagnostics in job scratch normalization-build.log. Root notified immediately for early push.
- Status reviewer found full stronger normalization already checked in `L_meta_4334.lean` (36,153 bytes, 714 lines). Its `priority_seed` helper exactly yields the first-gate cases needed by R670419, using only Mathlib+Defs. Preparing inlined component for integration; no need reprove generic cleaning.

## 2026-11-25T03:04:09.846276+00:00 — toolchain/search

Official Z3 5.3.3 installed in job scratch. Python exhaustive truth table confirms the explicit 16-gate monotone construction. `results/orch/lemmas/Search.lean` proves this upper bound with `decide +kernel`; `lake env lean` exited 0. This does not prove the posted 15-gate lower bound. Full log: `/tmp/oec/pequalnp-pilot-61/search-upper-lean.log`. A normalized 15-gate SMT search with first AND(0,1) is running; any SMT UNSAT remains computational evidence until independently certified in Lean.

2026-11-25T03:04:25.724314+00:00 status_review pivotal inventory update:
- Full priority normalization already checked in L_meta_4334.lean (36153B), exactly R670419 first hypothesis. L4336 is six AND suffix cases; L4338 is both NOT suffix cases (~513KB), leaving priority OR family L4340 unmerged.
- IMPORTANT: missing OR03 full lower bound already lives as helper L_meta_5120.bound, lines6138–6163, with NO reader-count premise. Its theorem: FanInTwo C -> first wire9 = x0||x3 -> circuitFun9 C = edge -> 16≤C.size. The final L5120 statement's reader-count hypothesis is unused. Thus every original first-gate case has a checked implementation somewhere.
- L2681.petersen_binary_lower lines3127–3146 proves arbitrary target circuit has 13 non-NOT gates. Binary-cost cases with >=3 NOT are therefore done mathematically.
- Shared machinery/certificate deduplication and total512KiB limit now main assembly issue. Finite_verification is extracting OR03 and assessing dedup; normalization agent informed about L4334; structural informed reader≤2 need not be proved for L5120 route.

## Restriction mathematics 2026-11-25T03:04:33.376413+00:00
- The six degree-three vertices form cycle 0-1-2-3-8-5-0. Vertices 4,6,7 subdivide its three opposite chords, so the graph is K3,3 with a perfect matching subdivided.
- Exhaustive finite independent-set calculation: deleting degree-two vertex gives 8 vertices,10 edges,alpha4 and star-cover upper cost13; deleting degree-three vertex gives 8 vertices,9 edges,alpha4 and upper cost12. These are upper formulas, not asserted general circuit lower bounds. True cofactors have corresponding upper costs10 and8.
- OR03 firstgate factors the star at4. Remaining graph G-4 has OR03 endpoints with disjoint neighbor sets {1,5} and {2,8}. Could reduce hard case to conditional cofactor bound if required.
- Generic direct-reader saving is already proved: Helpers/Readers.lean save accepts any clean circuit and finite set of gates reading constant-status wires; rc_input marks every direct input reader for either restriction value. Hence three distinct readers save three gates (clean NOT arity handled by simplification). Cofactor13 lower bound would imply at most2 direct readers for size15.
- Parent found unconditional L_meta_5120.bound for OR03; reader-count route paused in favor of fourteen-case assembly.

## 2026-11-25T03:04:58.522257+00:00 — full normalization component ready

`results/orch/lemmas/NormalizationFull.lean` (36,068 bytes, 713 lines) compiled with exit 0. Full empty diagnostics: `normalization-full-build.log` in job scratch. This adapts checked `L_meta_4334.lean` by renaming its namespace to `PEqualNP.Outside.L_meta_670.Normalize` and moving its final theorem inside as helper `normalization`. Only imports Mathlib and PEqualNP.Defs. `normalization` gives exactly the R670419 normal premise: a suffix circuit D with D.size+1 ≤ C.size, canonical NOT0/4 or six binary pair representatives, AND/NOT/OR priority restrictions, exact suffix evaluation with appended seed. Root notified immediately; component can be concatenated after removing duplicate import lines.

## 2026-11-25T03:06:24.491419+00:00 — computational search stopped

Full 512-row synthesis for 15 gates with first AND(0,1) returned UNKNOWN after 180.47 seconds (timeout). Two boundary-row CEGIS searches, one monotone with first AND(0,1), one at most two NOT gates with first NOT(0), were interrupted unresolved when all fourteen proved cases were located. No 15-gate witness or UNSAT certificate obtained. Search scripts and full logs remain under job scratch. Switching to self-contained raw proof aggregation.

## 2026-11-25T03:07:40.485490+00:00 — suffix-to-circuit bridge compiled

`results/orch/lemmas/Prepend.lean` compiled exit 0 (empty `prepend-build.log`). Namespace `PEqualNP.Outside.L_meta_670.Seed`. `seedCircuit D k a b` prepends the legal fanin-two seed gate. `seed_fanin`, `seed_size`, `seed_eval`, and `seed_first` prove legality, exact size increase by one, suffix evaluation equivalence, and semantic first-wire value. This lets Normalize.normalization feed every existing whole-circuit first-gate lower-bound case. APIs sent to assembly authors and root immediately.

2026-11-25T03:09:11.475395+00:00 status_review assembly:
- Exact L-meta-670 theorem footer authored at results/orch/lemmas/AssemblyFooter.txt (about2.9KB). Uses full priority normalization, Seed prepend bridge, NOT0/4, six AND cases, six OR cases including C5120.bound.
- Proof logic compiled in /tmp/oec/pequalnp-pilot-61/AssemblyTest.lean with real normalization/Seed and explicit theorem-shaped hypotheses for the nine case result packages; exit0 and no diagnostics. This is a conditional assembly check, not yet the unconditional full gap proof. No missing proofs or new axioms were introduced.
- Toolchain agent is inserting this footer into the fully inlined case aggregation; unconditional raw build remains outstanding.

## 2026-11-25T03:10:31.397295+00:00 Structural route pivot and compression

Confirmed L_meta_5120.bound is an unconditional first-OR03 size≥16 helper; the final theorem’s reader hypotheses are unused. Reader-bound proof is unnecessary for assembly.

Compression probe prepared in results/orch/lemmas/CompressionProbe.lean: copies the common L5120 verifier plus first small forest g15, and substitutes all columns × all paid masks for stored per-node rule pairs. Each candidate is still validated by buildRule_sound, so logical soundness is unchanged. Benchmark is serialized with other heavy Lean builds, uses -j1, and retains complete logs in job scratch.

Restriction_math found a stronger lossless representation: almost every opcode sequence is a one-step extension of a prior depth node. Parent index plus last opcode saves roughly90KB of hex text. Blocked offset tables and duplicate rule-list dictionaries are being quantified.

## 2026-11-25T03:11:11.150579+00:00 — aggregate integration

Initial fully inlined helper aggregate was 3,737,833 bytes. Namespace transformation preserved source cases and renamed source theorem endings to C{id}.outcome; no stale original module references remain. Its Lean run was intentionally interrupted (exit130) after~2min with no errors reported, sampled RSS8.2GB. Not a successful proof check. Switching to combinedcase files L2444(all six AND) and L4338(both NOT) instead of L1665/L1666/L4734; revised footer is being independently checked. All future large validation uses -j1.

## Finite verification 2026-11-25T03:11:40.590470+00:00

- Existing LRAT encoder is monotone AND/OR only, but first-gate files use a separate truth-table forest checker covering NOT.
- L5120 internal bound proves full OR03 case; its final readers restriction is redundant (status-review discovery).
- Initial nine-case raw assembly is 3.738 MB. Text/dependency-aware alias dedup produces 2.905 MB with 2790 aliases; numeric literal text 1.060 MB, alias text 182 KB. Dead-code closure saves less than 10 KB per case.
- Generic checked chunk/table batching helper compiled: results/orch/lemmas/Finite.lean. It can replace hundreds of repeated streamBlock and block_merge declarations while retaining the same Boolean tests and hints. Root notified immediately.

2026-11-25T03:11:40.811155+00:00 status_review combined assembly verified:
- Replaced separate NOT0/NOT4/allAND packages with combined C4338 (both NOT suffixes) and C2444 (six AND first gates). NOT pureinput restriction follows from Normalize.priority; no extra assumption needed.
- Revised conditional assembly harness compiled exit0 with empty diagnostics. Immutable snapshot: results/orch/lemmas/AssemblyConditional.lean; complete log: results/orch/assembly-conditional-build.log. Exact final footer: results/orch/lemmas/AssemblyFooter.txt. This remains conditional until the inlined case package compilation succeeds.

### 2026-11-25T03:12:54.972345+00:00 Compression probe checked

Baseline common verifier plus g15 certificate compiled in55.22s, peak RSS4519676KB. Replacing stored rule-pair lists by all columns × paid masks compiled in59.16s, peak RSS4523084KB. Both used Lean -j1, no new axioms or unproved assumptions. Complete logs are scratch compression-baseline.log and compression-allrules.log. Larger-case performance remains unverified.

## Certificate data compression 2026-11-25T03:14:35.323930+00:00
- Global generic compression is insufficient: selected AND/NOT/OR set uniquehex699415chars; rawbinary348400B, LZMA285792B (571584hexchars before machinery). Need semantic reconstruction/pruning.
- L4338 combined NOT proof has only35471hexchars despite513334B source; much source is reusable machinery, so prefer over separately inlined1665/1666 if statements fit.
- Parser /tmp/oec/pequalnp-pilot-61/packing_parser.py safely parses generated index-if trees and Packing headers, yielding exact stored-node prefix. JSON diagnostics packing-analysis.json and rule-dedup-analysis.json. Rulelist dictionaries save little; block16 offset scheme saves60745hexchars across6mainfiles.
- Major parentopcode compression: nearly every depth-d stored bank extends a depth-(d-1) bank at levelk+1. Store parent index and final10-bit op instead of10*d bits. Generator parent_prefix_analysis.py produces per-level compressed JSON and verifies every reconstructed opcode against original. Files L_meta_5120,4336,1674,1676,1677,1678 save88862hexchars total, before83tinyexception rows. Reconstruction depth≤8.
- Sorted unique(node,auto) pairs extracted from hashslots can replace full perfecthash tables via binarysearch of computed keySet(linkedSet). Saves~64500hexchars over5ORfiles, plusANDhash savings; runtime increaseslogarithmically. Sorting allnodes×autos instead is larger and should be avoided.
- Parent structural agent validated all-columns×paidmask rule regeneration on g15 (baseline55.22s vs59.16s). This removes rulepayload and offsets. Heavy depth3–5 blocks still need benchmarking; most fullgraphnodes have16–32paidmask choices and100+columns.

## Parent/rule codec 2026-11-25T03:19:52.828527+00:00
- Completed scratch encoder encode_parent_rules.py with agreed9field Packing layout (count,depth,columnWidth,parentWidth,indexWidth,offsetWidth,exceptionCount,exceptionPacked,data). Parent sentinel equals parentCount; newrulelist precedes all inherited ancestor rules. Extra valid rules retained, no deletionmask.
- Every original bank opcode and livebitset roundtrips in Python. Every original rule is included in reconstructed new+ancestor list, with no duplicatepairs. Missingprefix exception rows83total. Perlevel identical newrulelists sharepayload offsets.
- Actualhexbytes original→encoded: L5120 115872→72108; L4336 62600→44818; L1674 106528→68718; L1676 91027→58809; L1677 68558→46142; L1678 43094→26904. Outputs /tmp/oec/pequalnp-pilot-61/L_meta_<id>-parent-rules.json. About170KBsource savings including exceptions, before blockedoffsets.
- Cumulativeparent rulelists average~18.5candidates/node, max73, vsoriginal~3.4; significantly belowallcolumns×paidmasks. Column-only paidmaskenumeration averages~37candidates/node.
- Canonicalpaidmask trial L5120: greedyall exactlymatches10140/16090 storedrules; recursive-live cone10590/16090. Includingzero covers13867/16090(86.2%), leaving2223exceptions. Not yet compelling versuslosslessparent/rule codec. paidmask_analysis.py and JSONretain details.

### Finite batching and shared names 2026-11-25T03:20:41.232768+00:00

- Updated eight-case FullRaw baseline 3,329,775 bytes. batch_lean.py replaces 989 cellsBlock/block_merge declarations across 77 forests by lists of (count,arity,row-split,depth) plus generic proofChunks soundness; FullBatch 3,114,623 bytes.
- First rewritten C2444 g15 forest plus entire generic core compiled in FiniteBatchProbe.lean; same original leaf kernel checks, no algorithm changes. Full batch still needs full check.
- Dependency-aware definition aliasing plus batching gave 2,617,892 bytes before newest header change. open_aliases.py removes 1614 simple same-name aliases via 16 grouped scoped opens, saving 91,281 bytes. Private and noncomputable scoped opening tested in scratch.
- Root/normalization is standardizing three Live definitions and doing theorem-type dedup. Root/structural handles certificate data regeneration. These transformations are complementary.

## L4338 PackingT 2026-11-25T03:22:52.164419+00:00
- MainT table is only5layers/199nodes/7736hexchars. Slots42,39,36,33,30 are k14..10 withtmax0; parentopcode is atslot+3. Every196nonroot opcodeprefix matches,3depth1 roots needexception/basecase.
- Added packingT_analysis.py and encode_packingT.py. Exactopcode/live roundtrip and originalrule inclusion verified. Output L_meta_4338-packingT-parent-rules.json uses the same9field Packing layout, 5bitnr (maxnewrules15), and records actualslot plusparentSlotDelta3. Numericdatasize7736→5513chars, savings2223chars. SeparateLean decoder not worthwhile unlessnear512KiBthreshold.

### 2026-11-25T03:24:28.152219+00:00 Parent codec smoke check passed

ParentSmallProbe.lean passed Lean -j1 in56.46s, peak RSS4512236KB. It compiles the9field Packing representation and generic cmpOps/cmpRules reconstruction and checks the depth0 g15 certificate. Deeper recursion and representative search remain pending in ParentLargeProbe.lean (throughg383). Frozen sources/logs retained.

Eight transformed source candidates retain original namespaces in scratch parent-cases/. Total source saving165100bytes. L4338 is mostly proof machinery: its PackingT payload is only7.7KB, so an additional T codec saves2.2KB at most and is deferred.

2026-11-25T03:26:27.762163+00:00 status_review records:
- scratch normalize_records.py standardizes C2444/C1676 BoundPool, IndexTree, Forest to C1676 product/list aliases; C1678 BoundPool alone is standardized, preserving its List-based Forest for now.
- Records2444Prefix.lean compiled exit0 with all generic verifier lemmas through g15 data, independently of Live/Reach/Run conversion. Frozen source141582B; full build log results/orch/records2444-prefix-build.log.
- Original C2444 data:17 column trees,193 forks; Python checked every stored pivot equals flattened left subtree length. Thus List-based tree lookup agrees on actual data. Kernel replay of full certificate still required.
- Exact-text dedup measured24,469B saving from records alone,30,889B when composed after current Live unification. More sharing requires semantic/type-level dedup.

### 2026-11-25T03:27:54.585298+00:00 Further safe compression estimates

After parent-opcode and rule-inheritance encoding, one offset per16nodes with a bounded sequential header walk saves an additional28.7KB across7Packing-based files; it loses some interned-rule sharing but still wins overall. Not implemented or Lean-checked yet. Hash-table sorted-pair extractor delivered to finite_verification yields87.3KB additional numeric saving, Python checked against originallookup.

## 2026-11-25T03:29:23.033795+00:00 status_review record unification follow-up
- Combined prefixes regenerated using latest normalization Live/Reach/Run fixes: UnifiedRecords2444Prefix.lean and UnifiedRecords1678Prefix.lean. Compile pending serialized probe queue.
- Optional scratch normalize_forest1678.py converts C1678 Forest to canonical Array autos/List IndexTree representation and rewrites 17 data autos declarations; exact-dedup result grew 331 bytes, so this optional pass is not prioritized.
- Independent source-level parent codec review found no new assumptions or soundness gap: inherited candidates still pass unchanged buildRule checker; final Lean certificate replay remains required.

### 2026-11-25T03:30:09+00:00 — restriction_math: packed certificate utilities complete

Actual-key sorted hash records are generated by scratch `hash_records.py` for selected modules 2444, 4338, 1674, 5120, 1676, 1677, 1678. Every retained pair was checked against the original hash lookup at its actual stateSet key; only five equivalent-pair redirects occurred (1676), and the original returned pair is retained. Regular hash numeric source savings are about 87 KB. Finite_verification owns pure Lean integration. L4338 four tiny PackingT hash links remain in their original format.

Optional `block_parent_offsets.py` converts the existing parent/rule JSON into sequential new-rule payload with block-16 offset anchors. All opcode/live states and exact new-rule lists roundtrip. Seven selected modules save an additional 29,070 hex characters: 2444 4144, 4338 411, 1674 6644, 5120 5917, 1676 5676, 1677 4387, 1678 1891. Existing checked codec files are unchanged. Decoder replacement is `parent_rules_block16.lean.txt`; generated data are `L_meta_ID-parent-rules-block16.json`. All artifacts live under `/tmp/oec/pequalnp-pilot-61/` and root was notified to preserve them. No Lean builds were run for this optional variant.

## 2026-11-25T03:32:23.634305+00:00 — finite verification: sorted hash lookup

Implemented `/tmp/oec/pequalnp-pilot-61/sorted_hash.py`: replace stored perfect-hash shift/fingerprint tables with sorted packed `(node, permutation)` pairs. Binary search recomputes each candidate key from `stateSet` in an index-free copy of the same Forest. Existing same-state certificate checks remain unchanged. `SortedHashProbe.lean` (205817 bytes, generic core plus g15/g31 through valid31) compiled with exit 0; complete diagnostics are in `sorted-hash-probe.log`. No new trust assumption or runtime evaluator is used.

Composition candidates are `/tmp/oec/pequalnp-pilot-61/parent-sorted-cases/L_meta_<id>.lean` for 2444,4338,1673,1674,5120,1676,1677,1678. They compose structural parent sharing with sorted hashes. Combined saving over parent-only cases: 69308 bytes before common-helper deduplication. The tiny regular tables of 4338 alone grow27bytes due to helper overhead; shared-helper dedup should recover this. No full combined replay yet.

Added dependency closure `/tmp/oec/pequalnp-pilot-61/prune_lean.py SOURCE OUTPUT --report JSON --root FULLNAME ...`. It preserves namespace/section scopes and can isolate only arbitrary root declarations. On current pre-standardization TypeDedupCandidate, it removes1676declarations and162349bytes. Run after all type/graph-bound aliases for more meaningful certificate pruning. Fresh Lean checking is required for every pruned candidate.

### 2026-11-25T03:33:17.510532+00:00 Parent codec representative replay passed

ParentLargeProbe.lean passed Lean -j1 in182.45s, peak RSS4626096KB. It includes the complete L5120 verifier and all certificate forests throughg383; this exercises recursive opcode reconstruction and inherited rules across hundreds of states. Full log parent-large.log is retained. Root was notified immediately for a reviewed push.

Primary transformer: apply_parent_codec.py INPUT ENCODED_JSON OUTPUT [--namespace NAME] [--cut-before MARKER]. Source candidates with original namespaces are under scratch parent-cases/. Optional --block16 consumes corresponding parent-rules-block16.json and saves another29KB total; that extra format has Python roundtrip checks but no Lean replay yet. Sorted-hash transformer is owned by finite_verification and composes after parent encoding.

## 2026-11-25T03:33:22.371997+00:00 status_review preservation checks
- Executed actual outside-guard checkOwnNamespace on regenerated FullRaw.lean with source-isolating named sections inside the outer L_meta_670 namespace: PASS. Top-level sections remain forbidden; present arrangement is compliant.
- SortedHashProbe independent review PASS: 642 declarations unchanged from L5120; only g31 hash payloads/index changed plus three pure lookup helpers and an index-free Forest base. Soundness/certificate statements unchanged, so hash collisions cannot bypass sameWords and linkedSet checks. checkPlain PASS; complete build log has 259 warnings, zero errors; root observed exit0. SHA256 79c5c8f7879cf7bd62917e6c3499edeb05316f7900184d31068976c74c0fd47f. Partial g31 component only.

2026-11-25T03:35:25.603802+00:00: Closure resolver correction: dot-notation receivers now preserve arbitrary declaration prefixes, e.g. `inputs.getD` keeps `inputs`, and `pairs.any` keeps `pairs`. Earlier pruning size reports were provisional and require regeneration after this correction. Normalization is validating a definition-only closure in Lean.

### 2026-11-25T03:39:43+00:00 — normalization: checked shared graph bounds

Combined `UnifiedRecords1678Prefix.lean` passed Lean, validating Church Live/Reach/Run and canonical BoundPool. `LowerEqualityProbe.lean` (24,984 bytes, 287 lines) also passed with empty diagnostics: Lower, vars and graphGoal agree globally by rfl across C2444/C4338/C1676/C1678; the normalized C1674/C5120/C1677 group needs a short induction equating recursive Reach, then gives equal Lower propositions. The script `/tmp/oec/pequalnp-pilot-61/alias_lower_bounds.py` aliases 78 same-strength lowN theorems, inserting the checked Reach/Lower bridges where needed. Apply after Live/record normalization and before source dedup and closure. Full aggregate replay remains required.

2026-11-25 03:40 UTC — structural integration: coherent FullCompressed.lean v2 created from parent+sorted inputs; stages aggregate=3095655, batch=2880503, live=2888342, records=2888662, low-aliases=2881460, dedup=2324179, prune=2106844, open=2069807. Frozen input hashes, script copies, stage outputs and complete transform logs at /tmp/oec/pequalnp-pilot-61/integrated-v2. Independent composition audit checked Source sections, include/omit and alias-open scopes; no blocker. No aggregate Lean replay yet.

## 2026-11-25T03:40:13.915750+00:00 status_review combined records validation
- UnifiedRecords2444Prefix.lean PASSED Lean -j1 exit0. Frozen source and complete results/orch/unified-records-2444-prefix-build.log preserved. Combines normalization Live/Reach/Run with canonical product BoundPool/Forest and list IndexTree; all generic soundness proofs compile. Numerical certificates remain separate replay obligation.
- LowerEqualityProbe independent review: all119 copied model declarations match FullBatchLive normalized aggregate exactly modulo whitespace. Proofs identify four unrestricted circuit models separately from three normalized models; no unjustified equivalence between those two groups. Equalities introduce no hypotheses.

## 2026-11-25T03:46:05.487509+00:00 — parent plus sorted-hash composition checked

`results/orch/lemmas/ParentSortedLargeProbe.lean` compiled with exit 0. This checks the common L5120 core and certificates through `valid383`, including parent opcode/rule sharing and sorted-hash lookup together. Complete diagnostics: `/tmp/oec/pequalnp-pilot-61/parent-sorted-large-probe.log` (76270 bytes, warnings only). Process was last observed alive at3m12s and confirmed finished by4m30s; parent-only baseline was182.45s. Peak observed RSS3.76GB. All large g383 certificate blocks and resulting lower bound passed unchanged validation.

### 2026-11-25T03:47:04+00:00 — restriction_math: cross-model lower-bound transfer checked

`results/orch/lemmas/LowerTransferProbe.lean` passed Lean (`lake env lean -j1`) in 5.24 seconds, exit 0. `Transfer.normalized_lower` proves `C1674.Lower true roots T L → C2444.Lower roots T L`; NOT is simulated by OR of its freely available inverse twice, preserving the exact bank and gate count. `vars_eq` and `graphGoal_eq` are checked by rfl, yielding `Transfer.normalized_graph_lower (m L)` for the concrete graph statements. Integration snippet `/tmp/oec/pequalnp-pilot-61/lower-transfer.lean.txt`; complete log `lower-transfer-check-3.log` and timing JSON in the same scratch directory. Root notified immediately for early push; structural/normalization own aliases and integration.

Earlier dedup audit pinpointed ancestor-wide tail resolution falsely mapping `Exists.elim` to C4338.Binary.CircuitProof.elim and `he.symm` to C1673.Bi.symm. On frozen integrated-v2 input, dropping this heuristic saves 67,693 bytes; bounded fallback and no fallback yield identical aliases/output. Token normalization saves another 28,585 bytes. Finite owns shared script corrections.

## 2026-11-25T03:48:22.749709+00:00 status_review alternative NOT packages
- Replaced C4338 hypothetically with C1665+C1666 using exact NOT0/NOT4 firstwire conclusions, extended standardization, common lower aliases for masks<512, parent/sorted codecs, scoped token dedup and dependency closure. Source-only estimate: baseline1972376 bytes; alternative2013327 bytes (+40951). Without new codecs alternative2085119 bytes (+112743). Recommendation retain C4338.
- C1665/C1666 Lower models count explicit NOT gates and belong to unrestricted C2444 family, not free-NOT normalized family. C1665 mask bit9 adds negated x0 root; C1666 bit9 flips target coordinate x4. Specialized bounds intentionally not aliased.
- Isolated codec parser accounted for C1665 extra negated wire and tuple Forest syntax. Exhaustive opcode/live/rule roundtrips passed; all110 packing levels passed roundtrip checks, and hash reconstruction had no mismatches (37 tables6778 records for1665;36 tables4639 records for1666). No Lean compile claim. Scratch not-alternative-estimate/summary.json and complete stage logs preserve results.

### 2026-11-25T03:50:25+00:00 — normalization: compression measurements and next check

The theorem-statement alpha pass with conservative whole-name dependency resolution produced `integrated-v2/07a-type-open.lean` at 1,876,680 bytes (unvalidated aggregate), 193,127 bytes below the prior opened candidate. It still contains about 1,019 KB of theorem/lemma source and 481 KB of hexadecimal literals. Extending the parser to simple definition bodies saved only another 4,968 bytes, so that strategy was deprioritized. The checked normalized-to-unrestricted transfer from restriction_math lets `alias_lower_bounds.py --cross-model` share 90 lowN proofs with C1674 ordered before C2444. Generic definition equality tests now target the remaining C4338 function definitions whose leading lambdas differ syntactically from C2444 telescopes.

2026-11-25 03:54 UTC — integrated-v3 compiled replay began after parent renewal; actual plain/namespace guards PASS; first failures were only default heartbeat exhaustion on generated batched table proofs. Finite owns scoped-limit correction. Cross-model transfer probe checked, then reordered integrated-v5 pipeline produced 1943889 bytes with90 low aliases. FullCompressed.lean remains v3; versioned v5 preserved separately. Child now replacingC4338 Binary theory via checkedC1674 lower_slice/lift_ok and low383.

### 2026-11-25T03:56:23+00:00 — restriction_math: large Binary development replaceable

`BinaryCofactorProbe.lean` passed Lean exit 0 in 22.44 seconds. `C1674.full_lower_of_cofactor` derives normalized full-graph Lower14 from the existing normalized vertex7=false cofactor Lower13. Existing `lift_ok` checks the restriction Move `(zero, inputs.getD 7 zero,128)` and essential-input witness `(input7,4,132)` by kernel computation. `C1674.binary_count_of_cofactor` uses existing `extract` (already bounded by non-NOT count), `list_run`, and `contraction` to prove `14 ≤ C.gates.countP (fun g => !isNot g)` for any fan-in-two circuit computing the full graph. This replaces all use of the roughly 200KB C4338.Binary development; remaining tail count arithmetic is elementary list induction.

The probe copies only C1674 generic definitions/proofs, with no certificate forest data; its two new theorems are conditioned on `Lower true (vars 383) (graphGoal 383) 13`, discharged by existing `low383` during integration. Standalone snippet `/tmp/oec/pequalnp-pilot-61/binary-cofactor.lean.txt`; complete successful log `binary-cofactor-check-2.log`, timing JSON likewise. Root informed immediately for early push; structural owns integration and Binary deletion.

### 2026-11-25T03:58:45+00:00 — normalization: 151 generic function identities checked

`GenericDefEqualities.lean` passed Lean with 151 `rfl` identities between C4338 and C2444 main verifier functions, including Live/Reach/Run and cost/mass; 43 nonidentities were excluded from the exploratory probe. The successful file is 72,913 bytes, with full diagnostics in scratch `generic-def-equalities.log`. `alias_generic_definitions.py` consumes `generic-def-equality-passed.json` and replaces those C4338 definitions with aliases. Dedup fingerprinting must inherit the target key for a pure `abbrev name := @Known.Full.Name`, otherwise dependent proofs remain unshared.

A separate correctness fix now resolves the longest known prefix of a dotted identifier: clippedInputs.getD must track clippedInputs while retaining the .getD suffix. Unresolved local/library receivers remain literal. Prior type-dedup outputs that omitted this prefix dependency are obsolete. The corrected fresh source is CrossGenericTypeDedup.lean (2,130,665 bytes), pruned to 1,826,362 bytes before opening aliases; it still needs aggregate Lean validation and does not yet include Binary cofactor replacement.

## 2026-11-25T04:01:24.880930+00:00 status_review later OR01/Forest investigations
- OR01 alternate2828+monotone route blocked: C4338.monoPlain is ImpossibleT graph14 0, yielding only monotone≥15. It does not exclude zero-NOT OR01 circuit15; no general16 source located in expanded Monotone2 and explicit GateOp restriction census. Existing OR01 monotone derived proofs reuse1673 core.
- Optional1678Forest conversion to Array autos/IndexTree cols PASSED generic-prefix Lean exit0 (73warnings,0errors). Frozen UnifiedAllRecords1678Prefix.lean and complete unified-all-records-1678-prefix-build.log saved. However repaired-resolver size comparison on CrossGenericAliased yields1919773→1921689 bytes (+1916); original Forest already aliases C1674.Forest, converted aliases C2444.Forest. Recommendation retain original1678Forest.

## 2026-11-25T04:03:44.891541+00:00 status_review binary/generic preservation review
- BinaryCofactorProbe PASS:209 declarations match original L1674 modulo whitespace; two new results assume exactly normalized Lower(true,vars383,graphGoal383,13), use checked lift_ok to get full normalized lower14, then derive14≤number of non-NOT gates. Count/target agree with replaced C4338 Binary predicate; no added assumptions. Frozen snippet exactly matches checked probe suffix andv6 snapshot. checkPlain PASS, log17warnings/0errors, timedexit0 in22.445s. SourceSHA e85f10b1d02b0a10d4eb8195e77b2547c8eac047fb8f5a982386ab44581d4cd1.
- GenericDefEqualities PASS:151 unconditional rfl equalities; checkPlain PASS; log30warnings/0errors. SourceSHA 1e48626640760539ed376366609911a2e6646c02df06bb945953987ba4cd742e. Againstv6,412 model declarations identical and10 codec-related differences: only Packing/emptyPacking among aliases changed, with both sides currently literally identical nine-field product/zero values. Remaining readNode/nodeVerified/contextOf differences are not among151aliases.

### 2026-11-25T04:08:05+00:00 — restriction_math: parent-codec fast state repaired and v7 reviewed

`FastStateCodecProbe.lean` passed Lean exit0 in40.52s. Parent compression had changed Packing from8 to9 fields while the optimized `fastState` decoder in1674/1677 still read the old opcode layout. Checked replacement uses cmpNode for parent-layout live bits and cmpOps for reconstructed opcodes; corresponding fastState_eq proof adapts to9fields. Original1674/1677 blocks were byte-identical, so the one checked replacement applies to both. Root notified immediately to preserve artifact.

Frozen v7 independent static review passed: all manifest hashes match; the two input snapshots differ fromv6 only by this checked block (plus one trailing blank line), and final output differs only by the repair and pruning unused storedDepth. Final theorem type matches posted statement exactly modulo whitespace. No explicit sorry, new axioms, native_decide, unsafe/meta commands, forbidden root text, strings, or attributes; imports and limits conform. Full replay remains required. Review files: `/tmp/oec/pequalnp-pilot-61/v7-independent-audit.json`, `v7-final-review.diff`.

### 2026-11-25T04:09:51+00:00 — widened 5120 verifier replay passed

`Width768Probe.lean` passed Lean, covering the complete generic 5120 checker widened from 91 to 768 sample bits and certificate forests g15/g31 through valid31. New sample positions repeat original row90; 14 full-source sample arrays are adapted by `padSample` where bit90 is set. Opcode data and generated witness declarations remain byte-for-byte unchanged. The earlier literal92 witness state-bound hazard was caught before testing and fixed. Preserved successful component: `results/orch/lemmas/Width768Probe.lean`; full output: `results/orch/width768-probe-build.log`. Full-file certificate replay remains required before adoption.

2026-11-25 04:15 UTC — v7 repaired fastState has passed its former failure point in the full replay. Both real guard exports checkPlain/checkOwnNamespace pass; size1,935,481bytes remains overcap. Independent preservation review confirms exact theorem and checked block hashes. Optional width768 stage yielded v8 at1,913,207bytes; active v7 untouched.

### 2026-11-25T04:20:44+00:00 — restriction_math:297 ordinary-model function equalities certified

`OrdinaryGenericEqualities.lean` passed Lean exit0 in18.03s, proving297 whole-function equalities by rfl:151 C1676→C2444 and146 C1678→C2444. Initial404-comparison diagnostic reachedLean default100-error cap; a follow-up diagnostic checked the remaining tail, and only the final complete exit0 certifies the297 retained entries. No errors occurred in the cloned definition prefix. Certified map `ordinary-generic-equality-passed.json`, successful full log `ordinary-generic-equalities-2.log`, timingJSON, and isolated transformer `alias_ordinary_generics.py` are in scratch. Existing151 C4338equalities remain unchanged. Applyingnewmap to frozenv7/04c saves24,158bytes directly; theorem-type reuse may save further. Root notified immediately for artifactpush.

## 2026-11-25T04:22:08.376731+00:00 — normalized-core and live-mask analysis

Mechanical width transformer `widen_5120.py` standardizes91sample bits to768 by repeating sample row90; it pads70numeric samples across14arrays with a compact `padSample` wrapper. Generated rowPack/witnesses declarations are explicitly excluded and byte-compared against the original, preserving the genuine92state boundary in witnesses1903. Normalization independently compiled Width768Probe (complete core plusg15/g31), exit0. Fullcase replay remains pending.

Opcode entropy report:20107last-op records use201070bits. Best per-level fixed dictionaries save47067bits (~11.8KBhex), too small to drive the main reduction. Adjacent live masks offer a better codec:20022rows have a compatible prefix parent, and only3additional exceptions are required. Rechoosing parents while maximizing rule inheritance yields181555bits net saving (~45.4KBhex) including increased rule/offset costs. All20158nodes round-trip in Python with exact original ops/live and a superset of original validated rules.

Separate unvalidated live-codec candidates: `parent_live_codec.lean.txt`, `encode_parent_live.py`, `apply_parent_live.py`, `parent-live-cases/`, and `ParentLiveProbe.lean` under the scratch job directory. The helper adds cmpLive; the1674/1677fastState transform explicitly uses cmpLive. Packing remains a9tuple; exceptions now store full(op,live) pairs. Source saving41437bytes before helper dedup. Baseline source inputs are unchanged.

PackingT adapter: all199Tnodes have one unaryNOT at opcode step0; allremaining440ops are AND/OR. The op2,b15,out-of-range escape is absent from39887normalized opcode occurrences in1674/5120/1677. `repack_packingT_normalized.py` emits6245bytes of standard-parent data and an index adapter mapping k to3k; Python verifies all199signal banks under the proposed escape decoder. Normalization owns Lean soundness and terminal callback integration. This T data uses the currently checked full-live parent layout, not the newer live-delta candidate.

- 2026-11-25T04:22:55+00:00 toolchain: Found aggregation namespace bug: relative source identifiers `L_meta_1673.X`/`rho` survived full-prefix rewrite into C1673. Generator now replaces exact relative namespace token per source. Earlier2444/4338 and1673 have no simp attributes, ruling out prior simp registration as this failure cause.

- 2026-11-25T04:23:54+00:00 toolchain: Conservative custom-identifier minifier preserves imported-name components (138,240-name blacklist), structural declarations, and posted theorem namespace. Frozen v7 source1,935,481B→1,785,191B, saving150,290B via3,217 custom names. Reverse renaming reconstructs original source byte-for-byte. IdentifierMinificationProbe (568 names) compiled exit0, full log saved; full minified source not yet compiled.

## 2026-11-25T04:27:43.447116+00:00 — live-mask codec small replay passed

`results/orch/lemmas/ParentLiveProbe.lean` compiled with exit0 in60.756seconds, full generic5120core plusg15/g31 throughvalid31, combining samplewidth768, parent opcode/rule sharing, sorted hashes, and two-bit live deltas. Full log: `parent-live-probe.log`; exact timing: `parent-live-probe-build.json`; all20158node Python round-trip manifest: `parent-live-roundtrip.json`. Fullcase replay and1674/1677fastState proof check remain pending.

### Rectangle engine reuse feasibility (restriction_math, UTC 2026-11-25T04:31:32.417548+00:00)
- C1673 has only17 direct rawL occurrences. Its entire verifier core before rawP/rawL is seed-independent; downstream WZ/chk/imp_of can plausibly take rawL plus raw_good/m0_full witnesses. The rawS/rawT/rho symmetry witness is separately seed-specific. imp_full with FF avoids this symmetry but searches more branches.
- A whole-graph checker with rawP and no free seed may reuse existing seeded cofactor bounds by monotonicity (fewer initial signals). Root tests relaxing the proved packed budget limit L≤15 to L≤16.
- Computational diagnostics are scratch-only and contain #eval. RectangleOR04Experiment.lean compares unchanged baseline okE(70,8) with only rawL seed x0∨x4 substituted. RectangleOR04ExperimentSmall.lean similarly compares okE(38,5). Both remain running at this timestamp, so no success is claimed.
- VM compatibility replacements st(n,f)=f(n) and a projection-based pair are each proved equal to the source recursor versions by kernel proofs. Original proof code and certificates remain unchanged.

2026-11-25 04:33 UTC — v7 stopped atrootrequest after1318.976s, peakRSS4655132KiB, exit130; noolean. Correctedv12 usesrelative-IDfix, tokenfingerprints andforcedcomputationalaliases; postopen1,805,415bytes. Actualgenericprefixvalidation isownedby status_review. GenericImpossible feasibilityreport recommendsseed/chartparameterization first; observedremainingordinaryproofbudget47,912bytes.

### Semantic theorem reuse and alias-head diagnostics (2026-11-25T04:34:31.639929+00:00, status_review)

- Built a signature-only Lean diagnostic without axioms or admitted proofs: ordinary theorem bodies become harmless proposition-valued definitions, retaining exact declared telescopes, then Meta.isDefEq compares recovered types. Final cleaned diagnostic `SemanticDedupModel.lean` passed, with 514 comparisons, 290 positive rows, 189 distinct candidate aliases. These are candidates until original target proofs and actual alias wrappers replay successfully.
- Latest token dedup already absorbs 139 candidates; 50 additional typed aliases save 33,266 bytes after full closure/selective opens on frozen v12: 1,805,415 to 1,772,149. Candidate `SemanticV12Final.lean`; transformer `apply_semantic_aliases.py`; map `semantic-dedup-results-514.txt`. Actual five-case prefix `SemanticV12RealPrefix.lean` (341,951 bytes) is checking now; no full-proof claim.
- A pre-open prefix exposed why preserving canonical hashes while declining small computational aliases breaks original rw/simp proofs: C2444.neg and C1674.neg remained different heads while proof lemmas were shared. Forced computational aliases plus selective opens are necessary together. Structural owns the global fix (v12). Prefixes must be extracted after the full candidate's open pass, because qualified references can preserve aliases.
- Imported environment names were dumped before custom declarations into `imported-constant-names.txt` for safe name minification.

### Lazy rectangle checker passed — 2026-11-25T04:39:23.542739+00:00
The eager Bool.rec/List.rec VM experiments were stopped without results. Rewriting branch arguments and recursive list tails as Unit thunks, with generic kernel equality proofs, yielded exit0 in5.95s for both original OR01 okE(38,5)=true and modified OR04 okE(38,5)=true. This is one small cofactor computational check, not the whole gap theorem. Complete scratch log rectangle-or04-lazy.log and timingJSON retained; diagnostic source copied to results/orch/lemmas/RectangleOR04Lazy.lean.

2026-11-25T04:39:45.177337+00:00 normalization: LiveZeroBridge and TerminalNodeProbe passed Lean (exit 0). Weighted zero-NOT live runs are equivalent to normalized false-mode runs; generic node checker now supports arbitrary sound terminal callbacks. Building the ordinary-backend callback adapter, retaining paid unary prefixes and rectangle semantics.

2026-11-25T04:41:30.508044+00:00 finite_verification: ParentLiveFastStateProbe passed exit 0, C1674 generic core through fastState_eq. Full log scratch/parent-live-faststate-probe.log; timing 340.30s includes >=240s build queue. Source preserved results/orch/lemmas. Separate MonoNodeTablesProbe generated with original T contexts and shared normalized endingChecks + ordinary callback; waiting callback compilation before replay.

### Parameterized rectangle core passed — 2026-11-25T04:42:00.151732+00:00
RectangleParameterizedProbe.lean checked exit0 in30.71s, full log rectangle-parameterized-check-2.log. New11.6KB namespace Parameterized makes initial roots and prior-bound list arbitrary, assumes only segment goodness of the roots, allows L≤16, and provides root-set monotonicity plus old Imp→rawP Imp. The arbitrary prior list permits an already-proved same-mask(0,15) bound without circularity, although current constant-only elimination costs may make that cut computationally weak. Larger lazy VM comparison okE(70,8) also returned true/true for OR01/OR04 in7.00s. Whole-graph rawP-only chk0 15 t FF FF with old cofactors+(0,15) is now running with per-t progress and flushed output.

2026-11-25T04:43:20.569463+00:00 finite_verification numeric audit: SemanticV12Final has449212 hex characters; largest survivors are expected packedstate tables, not obvious dead originalhashdata. Profile scratch/semantic-v12-literal-profile.json. Newrule payload across livecodec is47590 pairs/486229bits; zero-mask tags save6.6KBhex, perlevel pairdictionary14.6KB beforehelpercost. Current best incremental codecs remain live delta~45KB and block16 offsets~29KB. No further codec changes made.

2026-11-25T04:45:56.633478+00:00 Structural: prepared attributed public PR12184 baseline using precise PEqualNP.Defs imported-name blacklist (129,921 identifier components). Reversible renaming shortens 1,020 identifiers at 5,791 occurrences; source 516,536 B becomes 484,952 B before added attribution, 485,260 B after attribution. Static plain/namespace/512 KiB guards pass. Finite independently reversed all 100,711 Lean tokens and confirmed all 14,443 numeric literals / 463 hexadecimal blobs unchanged. Frozen source results/orch/lemmas/CompactAttributedBaseline.lean, SHA256 89767951a2e9837b7b7291997481e50ee1c7e5e57b3a8478b3243e7564e002e2. Full Lean replay pending; toolchain profiles original-name equivalent. Both public candidate heads reportedly timed out in intake, so runtime improvement remains necessary.

2026-11-25T04:46:12.590992+00:00 finite_verification independent PR12184 review: CompactAttributedBaseline485260B; SHA25689767951a2e9837b7b7291997481e50ee1c7e5e57b3a8478b3243e7564e002e2. Reverse1020-name bijection reproduces all100711 source tokens; all14443 numeric literals (463hex) identical in order. Newnames and renamedoldnames do not collide with imported constant components. No forbidden tokens. Attribution present. Own kernelbuild stillrequired. Complete audit scratch/pr12184-independent-renaming-review.json. Rootforests761signed+2736monotone states; existingflatreader shouldremain forruntime.

### Compact peer runtime comparison — 2026-11-25T04:49:08.473545+00:00
Read-only comparison of PR12184 and PR12203 found different root certificates and checking strategies.12184 has2736 monotone-root states and761 signed-root states;12203 has1471 and698.12203 adds sound KW direct cuts via mixedForest, and dictionaries for opcode prefixes/live masks plus sorted hint lists, reducing hex text222410→155383bytes at the cost of a larger generic core. Kernel decide occurrences442→592 suggest finer splitting, but decoder overhead and KW costs need profiling. This is not a claim either full source has compiled or passed the repository checker. Full declaration reports and comparison JSON remain in scratch.

2026-11-25T04:49:12.457269+00:00 normalization: ForceBatchProbe passed Lean; four small helpers force packed signal/covariance Nats without changing Batch values. Standalone generic identities are checked; source-level change reviewed independently by structural and status_review. Whole certificate performance benefit remains to be measured before integration.

2026-11-25T04:49:15.847063+00:00 Structural: CompactMinificationProbe PASSED exit 0 in 42.535 s, peak RSS 3,245,716 KiB, through generic wholegraph engine and low15 certificate using exact complete-candidate name map. Source 159,195 bytes SHA256 c8604f9b1003602e10ff07183d29d81cea44f43c55650f1c958a0830581f5385. Full log and timing report preserved in results/orch; root notified immediately. Complete candidate replay remains pending. Oversized v12 marked superseded and explicitly unvalidated due selective-open alias-chain issue.

2026-11-25T04:54:38.815091+00:00 Structural: frozen CompactForcedCandidate.lean is 517,844 bytes (6,444 bytes under cap), SHA256 60678a7d6e1734d1f270e4b05bc4d4bedc090ed65bebceaee81ae34fe2b77f5e. Original helper names retained; explicit benoitrazet/PR12184/source-SHA/Apache-2.0 attribution added. Only functional patch is proved forcePacked/forceBatch identities plus rowCut forcing and two simp additions. Independent child audit restores exact original bytes after reverting these edits; all 463 hex blobs and complete final theorem/proof are unchanged. Plain, namespace, and size guards pass. Comparative timing and full candidate replay remain pending. Child additionally censuses repeated sample rows to assess a safe width reduction.

2026-11-25T04:57:01.596930+00:00 Compact benchmark lane: independently audited forceBatch and width278 changes. forceBatch inverse restores original public source byte-for-byte; width change is exactly27 core768→278 and25 stride769→279 tokens, with complete certificate suffix/final theorem unchanged. Script sample_row_census.py reconstructed all768 positive/negative pairs from17 arrays using modulo2^768 for negatives; g383 is worst with278 unique/prefix278, rootS274, rootM145. Independent modulo2^278 reconstruction retains exactly every original pair for every array. Full census, width inventory, and audit reports preserved in results/orch. No source mutation or Lean build from this lane.

2026-11-25T04:57:10.485806+00:00 Structural: full forced compact replay started with -j3 on CPUs2–3, explicit olean, complete scratch/compact-forced-profile.log and metadata JSON. Original baseline remains on CPUs0–1. Six-state benchmark source audit passes:168/170 dependency declarations exactly match respective full sources, identical target, no forbidden constructs. The16-state comparison reportedly gives only~2% CPU improvement, so no whole-proof speed claim is warranted yet. PR12203 fallback forceBatch interfaces are all byte-identical and exact transformer applies; patched raw size524508B exceeds cap by220B before credit, so that fallback would need small compression.

2026-11-25T04:57:28.023044+00:00 normalization: ForceBatchIntegrationPrefix and Width278IntegrationPrefix both passed Lean, exit0. Width patch changes exactly40 generic-core lines (27 width768→278 tokens and25 lane769→279 tokens), preserves every512 token and byte-identical full certificate suffix. Structural child independently verified all17 sample arrays retain every original pair at width278; rootM needs145 and rootS274, maximum g383278. Matched numerical runtime benchmark pending; active full768 replays remain frozen.

2026-11-25T04:59:52.357059+00:00 Compact benchmark lane: fallback PR12203 already declares Bits152. Correct declared-width census covers18 sample arrays, worst sgY152 unique pairs/prefix152; rootmoY88. Therefore the width278 reduction is specific to PR12184. Merely widening PR12203 positive152-bit literals would introduce unwanted zero sample pairs. Census CLI now infers the exact Bits width by default and records any explicit override; full fallback census saved as pr12203-sample-row-census.json.

2026-11-25T05:00:00Z root re-plan: oversized 14-case assembly is superseded by the attributed shared-mode compact proof. Original and forceBatch full builds run on separate CPU pairs. Width278 generic proof and a numerical leaf pass; all checked components are pushed. New runtime lanes target larger same-arity batches and decoded-context caching, because the repository verifier serially rechecks all project declarations within the 1200s intake budget. No complete gap proof or checker acceptance has been claimed.
