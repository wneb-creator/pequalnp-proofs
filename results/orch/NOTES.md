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
