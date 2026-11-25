# L-meta-6349 orchestration notes

Lease acquired 2026-11-25 05:33:42 UTC. Root alone handles desk calls and submission.
Target: graph mask 5805 on Fin 4 × Fin 4 has RepSizeAtMost 10 and not RepSizeAtMost 9.
Allowed project import: PEqualNP.Defs. Named file: lean/PEqualNP/Outside/L_meta_6349.lean.
Subagents append findings below; use distinct scratch Lean files under results/orch/lemmas.
Final PR tree must add only the named file; orchestration artifacts may be preserved in earlier branch commits.

Build environment:
- PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-69/lean-4.36.0-linux/bin/lake
- PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-69/build-state
- prepend /tmp/oec/pequalnp-pilot-69/lean-4.36.0-linux/bin to PATH
- Full Mathlib cache and checker/Defs prerequisites are built. Never lake update.

Rules: exact statement, no sorry/axioms/native_decide, no forbidden text, helpers in own module namespace, qualified theorem last. Save complete diagnostic output to scratch. Inform root immediately when any own Lean component compiles so it can be reviewed and pushed.

- Upper strategy: exhaustive formula-cost DP over all 16-bit masks found tree/formula minimum 11 for mask 5805, so the 10-gate witness needs shared intermediate gates (DAG). Searching circuit synthesis next.

## Lower-certificate route (05:36 UTC)

Promise.rep_lower44 is not in allowed imports. Reuse the already accepted L_meta_5531 inlined helper prefix through end LRAT.Promise, renamed to L_meta_6349_aux. This avoids new data types. Prefix is being compiled in results/orch/lemmas/LowerCertificate.lean. Finite-search agent owns exact enc2 bound9 CNF and LRAT generation; bundled cadical is available.

## 2026-11-25 05:35:26 UTC — status_review import and reuse audit

- Promise.rep_lower44 exists at Library/LRAT/Promise.lean:38, but PEqualNP.Defs imports none of Library/LRAT. The advertised bridge is not directly available under the sole allowed project import; its definitions/proofs must be copied and namespaced if used. Accepted L_meta_5531 does that in 3,571 lines.
- The statement itself uses available Defs.Represents definitions. RepSizeAtMost quantifies arbitrary Circuit, Monotone2, size bound and Represents. Constants, singleton gates, missing-wire reads and arbitrary output indexes are included; lower proofs must account for them.
- Accepted L_meta_6299 (626 lines), L_meta_6304 (651), L_meta_6332 (730) prove exact table costs 9 from only Mathlib + Defs via self-contained build/live compression, BitVec positive-negative pair cuts, optimized search and cached leaf lists, checked by decide +kernel. L_meta_6379 (2461) uses a different finite technique for cost 8.
- RepSizeAtMost table census saved to /tmp/oec/pequalnp-pilot-69/rep-census.json. No exact mask5805 theorem found. No cost >=10 among detected one-line exact table theorem declarations.

2026-11-25T05:35:50.294172+00:00 finite_search: mask5805 rows are [13,10,6,1], bipartite graph C6 plus pendant path length2. True promise rows [17,65,129,34,130,36,68,24]. Exact enc2 n8/s9 SAT search launched with repo genmono adapted only g and ROWS, flags rows,lex. CNF/proof/logs under scratch5805-9.*. Solver is official Lean bin/cadical --lrat --no-binary.

- 2026-11-25T05:36:04.817003+00:00 Enumerative route: adapting accepted L_meta_6299 live-compression search to mask5805 with 64 positive-negative pairs (128-bit traces). All eight inputs appear essential by separation; using that to eliminate initial-subset enumeration. First compiling generic search soundness and conditional lower bound.

- 2026-11-25T05:36:15.210653+00:00: Upper bound completed and Lean-checked in results/orch/lemmas/Upper.lean. 10-gate DAG found by SAT; independent 16-bit evaluation gives 5805. Lean file uses only PEqualNP.Defs, simp for Monotone2 and kernel decide for size/evaluation; exit0 with empty stdout/stderr. Root notified for early push.

## Structural route (2026-11-25 05:38 UTC)

- Mask5805 is C6 plus a 2-edge tail, all8 input lines forced. Generic RepReads/RepPath bounds only7/8 respectively.
- Checked accepted table-theorem masks for row/column permutation or transposition equivalence: target orbit has576 masks, canonical minimum5805; none matched an existing checked table row.
- Existing L_meta_6379 and L_meta_6014 provide reusable self-contained finite Live-state certificate methods.

- 2026-11-25 05:36:25 UTC: LowerCertificate.lean helper engine compiled, exit 0, empty stdout/stderr. Root notified for early preservation. No target bound asserted yet. Logs lower-engine.stdout/.stderr.

## 2026-11-25 05:37:01 UTC — status_review independent partial push review

- Upper.lean and named L_meta_6349.lean are byte-identical, SHA256 2c766929e8286bf20de1ac078ea78c0a800becd601c6143c40e8a165efd7f45a. Independent simulation of all 16 promise inputs yields exactly mask5805. Circuit has ten gates, every gate AND/OR with two strictly earlier wire inputs, output17. Import and own-namespace syntax are valid; no forbidden content.
- LowerCertificate.lean SHA256 d0ebe915f2f5d8714cdf5c1330bf40f3834062ca53cafee83d54e9cb440f2ba8 (100,758 bytes) matches accepted L_meta_5531 helper prefix through end LRAT.Promise exactly after namespace renaming and omitting comments/blank lines. Complete compile log has zero error lines.
- Both are partial artifacts only. The upper file proves the bound10 half; engine has no mask5805 unsatisfiability certificate or target theorem. Standard format guard correctly refuses the absent final fully-qualified theorem. This is not a final proof/checker acceptance. Independent verdict: READY FOR PARTIAL CHECKPOINT PUSH once root confirms named module build; final PR must remove results artifacts and contain exact complete theorem.

- 2026-11-25T05:37:03.793842+00:00 Enumerative partial compiled (522 lines): circuit-to-live compression, search completeness, all-eight-inputs-essential, lower bound conditional on optimized9=false. Exact C++ mirror found no circuit with 9 gates over 28 first-pair branches in 0.027s (~128k search calls); now kernel-checking 28 decision chunks in EnumerativeFull.lean.

## 2026-11-25 05:39 UTC — lower_certificate independent enumerative audit

Reviewed Enumerative.lean (522 lines) and all28 chunk assembly in EnumerativeFull.lean. No soundness/completeness defect found. gate_table/classify cover empty, singleton, binary gates, constants, duplicated operands, missing/future wire reads; compile covers arbitrary outputs. Constants can be discarded because goal is nonconstant and Boolean identities are proved. compress keeps a live subset, extend_live covers size at most9, cuts_full proves every separation pruning obligation, essential_inputs kernel-checks all256 input sublists, optimized_complete proves keep-choice and extra-budget pruning complete. The28 first pairs cover all pairs of8 inputs. Final lower follows unconditionally when the kernel chunks compile. LRAT/AMO work paused in favor of this much smaller certificate route.

2026-11-25T05:38:29.700953+00:00 finite_search: independent Python16-bit truth-table live search returned false at gates9/extra2 (accepted goal anywhere in live pool, slightly larger acceptance than Lean singleton rule), all256 input subsets checked and only full8-input subset separates all positive/negative pairs. Independently recomputed all8 rawInputs BitVec128 values from mask5805; exact match. Script/logs independent_live_search.py and independent-live.stdout/.stderr under scratch. Both huge CaDiCaL traces halted cleanly at root request; preserved full logs and incomplete traces.

## 2026-11-25 05:38:45 UTC — status_review independent enumeration audit

- EnumerativeFull generic engine through optimized_complete is identical to accepted6299 modulo own namespace, 120/60 to128/64 dimensions, and regenerated trace data. Independent script verified all128 trace bits against oneEach rows and goal bits against exact mask5805.
- Independently checked all256 initial input subsets: only all8 inputs separate every positive-negative pair. The proof uses cuts_full to justify this pruning. All28 unordered pairs are covered exactly once by chunk_0 through chunk_27.
- Independent Python implementation of optimized9 2 returned false in1.82seconds (32,496 memoized states). This supports, but does not replace, the pending kernel computations. Constants, unary/repeated inputs, arbitrary reads and outputs are handled in gate_table/classify/compile.
- No semantic or forbidden-format defect found. Current standalone helper file lacks final qualified target theorem, correctly refused by format guard for that sole reason. Ready for checkpoint if compile succeeds, then integration with reviewed upperBound and exact final conjunction.

## Structural route paused (2026-11-25 05:38:56 UTC)

- Parent reports a compact enumerative lower certificate, independently crosschecked, and compiling28kernel chunks. Paused analytic route.
- Independent formula DP gives target5805 minimum11 formula gates (constants free), and induced C6 minimum8 formula gates. C6 has a7gate shared circuit. These are computational findings, not Lean-certified results. Full scripts/logs under scratch formula_min.* and formula_cycle.*.
- Possible theoretical proof route would strengthen induced-subgraph elimination to charge3 for the2-edge pendant path; generic elimination charges2, insufficient. No extra source changes needed for this route.

## 2026-11-25 05:43:28 UTC — status_review chunk0 checkpoint audit

- EnumerativeChunk0.lean (528 lines; SHA2564d5de2f6d09579208fbbe986a95b91d624792710611e230c157a8c4a67f002f9) is a subset of previously reviewed EnumerativeFull, modulo removal of blanket Mathlib import. It contains the generic engine and conditional lower bound, pairOK and chunk_0 only. Full compile output records kernel check7.43s, no errors.
- Format guard finds only intentionally absent qualified final theorem. Independent verdict: READY FOR PARTIAL CHECKPOINT PUSH. Remaining27chunks and full lower theorem are still pending; this is not final proof acceptance.

- 2026-11-25T05:43:43.835959+00:00: upper_bound returned for kernel-memory work; ChunkAssembly.lean compiled (only Defs import). Adds exact cut-valid children list, optimized_step_eq equivalence, optimized_of_children closure. Passed exit0 empty logs. toolchain_setup/finite_search integrating bounded leaf chunks and DAG state references; no deep evaluation needed for internal nodes.

## 2026-11-25 05:44:03 UTC — status_review child assembly audit

- ChunkAssembly.lean (566lines; SHA2567f869b981a4234d91b1325cf8ab6ed83c873853c057dd63f3b4b441b0db98d81) starts with byte-identical reviewed generic prefix after Mathlib removal. New childChoices lists exactly the four dispatch alternatives, with matching separation guards and extra-budget decrements; children includes every unordered pair and both ops. optimized_step_eq is exact equality retaining the terminal-goal branch. optimized_of_children requires terminal-goal false and all immediate children false, so no case is omitted.
- Compiled exit0 reported by builder, empty complete logs. Guard only refuses intentionally absent final qualified theorem. Independent verdict: READY FOR PARTIAL CHECKPOINT PUSH; no full target claim.

- 2026-11-25T05:44:28.639106+00:00 Enumerative raw28chunk run stopped at15.7GB RSS. Selective-import single1030-callchunk passed under4096MiB in7.43s kernel. Adaptive1350-node proof DAG generated (282264bytes) using119 shared128-bit traces; testing worst982-call leaf and one-step assembly before full build.

- 2026-11-25T05:45:39.212933+00:00 Adaptive DAG tests passed under4096MiB: worst982-call leaf kernel3.99s;49-proof internalassembly kernel12.2s. FullEnumerativeDAG.lean immutable candidate282264bytes, SHA256 9610e6362fe20d06a0c4cb26eb57bd5a2461bd5f93bf2305fc37cbd54f6857e4. Root will integrate and run named lakebuild directly; no duplicate standalonefullrun.

## 2026-11-25 05:46:23 UTC — status_review DAG candidate audit

- EnumerativeDAG.lean immutable SHA2569610e6362fe20d06a0c4cb26eb57bd5a2461bd5f93bf2305fc37cbd54f6857e4 (7713lines282264bytes). Generic prefix exactly matches reviewed ChunkAssembly. All119 trace constants fit128bits. State/proof IDs each cover0through1349 exactly, final state is the exact8input list with optimized9 2.
- Independent Python audit recomputed all1311leaf searches as false, all39internal child lists exactly (including order/duplicates), and all1428internal references. Every referenced proof is earlier and has matching decremented gate bound and extra budget. Root covers every search child; no assumptions or omitted cases. Audit completed0.99s,32457memoized search states.
- Format guard finds only absent final qualified theorem. Verdict: READY FOR NAMED FILE INTEGRATION AND BUILD with reviewed upperBound and exact target conjunction. No full compile/checker acceptance yet; root must run both before final push.

## 2026-11-25 05:47:35 UTC — status_review final integration and generic memo audit

- Named full candidate SHA256c47d7e7ccb6f5373653f1b4633a1a179ad7b253448a2eb609c00a51177f780bd is exactly reviewedUpper plus reviewedDAG plus final theorem whose statement is byte-identical to assigned gap.statement. Final proof conjoins reviewed upperBound and Enum.lower. Independent format guard PASSED. Full named build/checker still pending.
- EnumMemo.lean SHA2569576924293e3439e90ec98024abd71635b2c1837b99b758ab52591284394d7cf has exact reviewed generic prefix, then a sound finite-table certificate: treeMem_sound requires only successful membership, no unjustified search-tree ordering; sorted preserves finset and Nodup; certificate_sound inducts on strictly decreasing natural gate count, preventing circular lookup. All successor alternatives follow dispatch_complete and gate-budget arithmetic uses live_card. Only conditional certificate soundness, no full target proof yet. Compile logs empty, builder reports exit0. Guard only expected absent final theorem. READY FOR PARTIAL CHECKPOINT PUSH.
- Latest structured gh pr list search6349 (allstates,limit1000) returned0rows, complete under limit, no stderr.

- 2026-11-25T05:49:52.281910+00:00 All39 internal DAG assembly schemas kernel-checked under4096MiB with explicit child-proof parameters, including82-way root. Independent reviewer verified1311 leaf searches,39 childlists,1428 earlier-child references,119traceconstants. Named finalbuild nowrunning; monitored Leanpeak5.35GiB plusLake0.86GiB at05:49UTC, noerrors.

## 2026-11-25 05:51:37 UTC — status_review compiled memo checkpoint audit

- EnumMemoChecked.lean SHA256e8b9dd8ad87d07d7b26da1994f6b6f04be0bf24c733c9bc092dd559ef86afb93 matches source snapshot exactly through table data. Versus reviewed genericMemo, only sorting changes mergeSort to insertionSort with matching Mathlib permutation proofs; semantic certificate argument unchanged.
- Parsed actual Lean literal tree independently:298trace constants,4270unique states, valid lexicographic tree ordering, exact sorted9gate input state present. Recomputed every table node check independently: all true. Only48states are asserted kernelchecked in this artifact, in16-state batches at offsets0,2000,4200; it makes no full lower-bound claim.
- Complete enum-memo-profile compile metrics reportexit0,24.26seconds,4139896KiBmaxRSS. Guard finds only intentionally missing qualified final theorem. Verdict: READY FOR PARTIAL CHECKPOINT PUSH. Full-table data consistency is independent computational evidence, not a complete Lean proof yet.

## 2026-11-25T05:53:23.391962+00:00 — compact memo closure certificate

The4270 canonical states have298 distinctW128 trace values and15625 feasible successor edges; independent Python closure found zero missing successors. Generic EnumMemo.lean certificate_sound proved by induction onremaininggates, using sorted-finset preservation and existing live/dispatch completeness. Direct16-state batches with global entries/drop passed butcostgrewlinearlywithoffset. Replaced by175namedsubtrees of≤32nodes and174stem assemblies, withnoncomputabledata defs toavoidunneededIRcompilation. Three subtree batches covering 64 states kernelchecked in1.44s, fullcompile14.18s,peak3.31GB. Completecandidate EnumMemoComplete.lean is327480bytes/2906lines,sha256cc336f61b9be618c9a627106ce7134bc32a7884ed573b2f78be2fa81ae3e4bc8; full-M4096 compile underway, independentstatus_reviewaudit underway.

## 2026-11-25 05:53:47 UTC — status_review complete memo subtree assembly audit

- EnumMemoComplete.lean immutableSHA256cc336f61b9be618c9a627106ce7134bc32a7884ed573b2f78be2fa81ae3e4bc8 (327480bytes2906lines). Certificate genericprefix and298paletteconstants unchanged. Independently parsed every named subtree; expanded table is exactly the previously audited4270-state tree.
- All175blockproofs are closed decide+kernel checks, cover4096entries, eachblock≤32nodes. All174stemproofs use all_entry_node with exactmatching children and pivot, coverthe174remaining entries, reference only earlier stems. No missing states or omitted pivots. Final lower uses ok_stem_173 for full table and exact9gate root membership.
- New lower_of_certificate bridge follows compression, essential_inputs, sortingpermutation and certificate_sound. all_entry_node explicitly combines leftlist,pivot,rightlist. No semanticdefect. Format guard only absentqualifiedfinaltargettheorem. Verdict READY FOR INTEGRATION conditionalonfullcompile; fullchecker stillrequired.

## 2026-11-25 06:00:31 UTC — status_review subtree checkpoint audit

- EnumMemoTreeTest.lean SHA25655e1abbb82acb5f3f9aff16400da0da7cb3c6e9a2311db66fd21d7de89826ed5 prefix and entire decomposed table exactly match reviewed CompleteMemo. Closed checks are blocks0,60,127. Actual sizes are16+32+16=64checkedstates, correcting earlier72estimate.
- Full subtree assembly/data has already been independently verified; this artifact asserts only those64closed nodechecks and no complete target. Guard only absentfinalqualifiedtheorem. Verdict: READY FOR PARTIAL CHECKPOINT PUSH; checkpointmetrics should say64states.

## 2026-11-25 06:01:56 UTC — status_review fresh-output pruning audit

- EnumerativeFreshPrefix.lean SHA2567ca107654f3e820883b7bfe77c7ac508f4e8fa71c9351dfaf191760272161979 (575lines) differs from reviewed ChunkAssembly only by EnumFresh namespace and rejecting a generated trace already in current a::b::r. Completeness supplies hnew directly from live-step requirement z∉s and permutation membership. Both Boolean dispatch and childlist add identical guards, with updated childChoices_eq proof. No legitimate live step is excluded.
- Full compile output has only two if_neg deprecation warnings, no errors; builder reportedexit0. Format guard only expected absentfinalqualifiedtheorem. Verdict READY FOR PARTIAL CHECKPOINT PUSH. This is a generic engine and conditional lower bound, no complete target claim.

2026-11-25T06:02:13.948304+00:00 finite_search: fresh-output-only pruned search returns false; 72,404 recursive calls, 28,301 unique ordered states. Threshold 1000 gives 883 selected states (25 internal, 858 leaves), 71,719 leaf calls, 104 shared truth tables; threshold 500 gives 1,554 selected states (58 internal, 1,496 leaves). Data: ordered-pruned-dag-500.json and ordered-pruned-dag-1000.json under scratch. Sole search change is skip output z already in current ws before considering retention modes. Original order, mask, samples, and all other pruning are unchanged. Child references, decreasing depth, capacity invariant, freshness, absence of target, and leaf thresholds all independently validated.

## 2026-11-25T06:02:16.870391+00:00 — complete lower bound checked

EnumMemoComplete.lean (SHA256 cc336f61b9be618c9a627106ce7134bc32a7884ed573b2f78be2fa81ae3e4bc8) compiled with exit 0 under -M5120 in 239.18 seconds. Peak Lean RSS 5,133,704 KiB; aggregate 5,969,864 KiB (~5.69 GiB). All 4,270 cached states and 15,625 successor edges are covered by 175 checked subtree blocks plus 174 checked pivots. This proves the unconditional lower half for mask 5805 at bound 9. Root notified immediately for checkpoint and integration. Complete logs and resource samples: enum-memo-complete5120.* in scratch. The earlier -M4096 run reached its explicit memory cap, a resource failure only.

- 2026-11-25T06:02:32.737350+00:00 Enumerative raw28chunk run stopped at15.7GB RSS. Selective-import single1030-callchunk passed under4096MiB in7.43s kernel. Fresh-output-pruned883-node proof DAG generated (193230bytes) using119 shared128-bit traces; testing worst982-call leaf and one-step assembly before full build.

- 2026-11-25T06:03:16.705351+00:00 Enumerative fallback work stopped on root instruction after canonical Memo route compiled in239s. Fresh-output prefix and worst954-call leaf both compile under4096MiB (leaf kernel9.77s); no full fresh-DAG build was started. Original ordered-DAG named build was stopped as superseded, without a verdict. Generic compression/completeness remains the foundation of the selected memo proof.

## 2026-11-25 06:03:42 UTC — status_review compiled memo integration and wrapper audit

- Named target SHA256850f99a46ae6297423188e19802af7f10561d88ba353e7d987ca87e3e30fc2d5 exactly combines reviewedUpper and compiled auditedCompleteMemo. Final target statement byte-identical to assignment, theorem uses only their conjunction. Independent imports/plainfile/ownnamespace guard PASSED. Ready for finalvalidation/push once namedbuild andchecker pass; no source edits needed.
- EnumMemoNamedGeneric.lean SHA2560fd7aeed5f8485e9fb7a2f354833f0ef8a191e3e2527c73ebed11d5c389591da (691lines30484bytes) genericprefix exactly matches compiledFullMemo, then all_entry_node_named merely rewrites explicit equality whole=.node x l r and applies existing all_entry_node. Sound wrapper, no new proof assumptions omitted. Compilelogs empty; builderexit0. Guard only missingfinalqualifiedtheorem. READY FOR PARTIAL CHECKPOINT PUSH; fullwrapper-basedcandidate untested and not selected forsubmission.
