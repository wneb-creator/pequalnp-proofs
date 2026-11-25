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
