# L-meta-2590 whole-tree preservation review

Verdict: PASS for preserving the versions listed in `REVIEW-final.sha256`. This is a preservation review after lease loss, not proof acceptance or a new mathematical result. No search, solver run, proof development, or Lean build was started for this review.

Scope: all 165 files then present in `results/orch2590`, plus the named Lean file: 166 files totaling 3,198,503 bytes. Every listed file was unchanged at the final hash comparison. This review and its manifest are additional text records and do not hash themselves.

All files are UTF-8 text without NUL bytes. Source/diagnostic inspection and credential-pattern scanning found no credential values, private keys, authenticated URLs, executable binaries, object files, or serialized solver binaries. The DIMACS archives are text. Python source parses successfully. Existing manifests match: all 47 auxiliary AND-search files and all six global search source/data hashes.

## Checked versus unverified Lean

The named `lean/PEqualNP/Outside/L_meta_2590.lean` is byte-identical to the independently reviewed `FirstNonbelow.lean`: 208 lines, 8515 bytes, SHA256 `467f08e4ac241a1d89271814490138f2f48573d41af36e8017d113f366b1fd83`. Its standalone check succeeded before the stop, with complete empty stdout/stderr. Root did not start a new named-module build after lease loss. Only Defs is imported, the namespace matches the gap, and the forbidden-format scan found no issue.

`REVIEW-preservation.md`, written by status_check, is retained unchanged as the independent semantic review of FirstNonbelow and EdgeAnd. The former explicitly assumes AO2, a lift fixed point, liveness, edge productivity, and input freshness. It does not establish those assumptions or the posted size20 lower bound. EdgeAnd is a generic raw-conjunction helper.

Successful component checks also include the conditional nine-variable floor bridge, monotone circuit extraction, and the extension with an explicit cofactor-floor hypothesis. The scratch test files importing Binary17 or MonoBase are archived test harnesses, not allowed final imports or proof PR files.

The actual `MonoBase.lean` export was interrupted with reported exit130. The 7398-line, 519562-byte `Mono18.lean` concatenation remains UNVERIFIED, even though its source was independently reviewed and its smaller components checked. Neither the general18 nor first-AND19 claim may be reported as a completed unconditional check of that full concatenation. Neither would prove the posted20 target in any event.

`Or13.lean` was also terminated with reported exit130. Its empty stdout/stderr do not mean compilation succeeded. The draft and interrupted logs are correctly labeled; no Lean validation of its final correctness theorem is claimed.

## Computational witness and searches

The 24-gate witness and its simplified 23-gate form have separate complete exhaustive1024-input validation records and an independent review using1024-bit truth vectors. Both source JSON hashes match that review. The simplified form has13 OR and10 AND gates, valid backward references, and all gates live. It refutes the auxiliary unconditional OR≥14 claim only; 23 gates does not refute the posted total-size≥20 claim. The possible22-gate absorption rewrite remains explicitly unverified and was not performed after stop.

The global19-gate SAT split has three completed UNKNOWN results, not UNSAT. The fixed19-gate stochastic run reports280,262,000 coordinate updates and best error score1; this is an empirical near miss. The nonlinear total-size optimizer was compiled and exercised only in a zero-second baseline; no long run was started.

The AND-count auxiliary model counts AND macros with unrestricted OR aggregation, not total binary gates. Its five-AND and dual-thirteen tests are UNKNOWN. Its UNSAT outcomes are zero/pinned sanity cases, and the separately recorded ten-AND nonread1 model is validation data. No unrestricted six-AND/nonread1 search began. README and result records consistently retain these limitations, with full solver/driver streams and text CNFs preserved.

## KW experiment

The saved rational matrix has reported feasible total weight20 and maximum permitted rectangle weight1; its script reconstructs rational entries and checks feasibility exactly after the numerical LP. The separate equality experiment symmetrizes the matrix and records1400 tight rectangles, then reports HiGHS infeasibility for an integral partition. The latter has no independently checked infeasibility certificate and is explicitly UNVERIFIED as a formal theorem.

These files concern formula leaves/monochromatic rectangle partitions. Neither the numeric20 objective nor the exploratory infeasibility result is presented as a circuit-size bound or a Lean proof. The exact scripts, JSON, stdout/stderr, and `kw-notes.md` preserve that distinction. No LP or MILP was rerun during this review.

## Final status and lease record

The full diagnostic response contains HTTP410 and the exact body message `no such live lease: it expired or was released. Ask /desk/next again.` It does not determine which cause occurred. Headers and body are preserved without credentials. The final NOTES, TIMELINE, validation record, and stopped-agent reports agree that work stopped after the confirmed failure.

The final status is compiled helper partials, conditional checks, unverified interrupted assemblies, and explicitly scoped computational research. The exact target theorem is absent. The local checker was not run on this incomplete target, no accepted verdict is claimed, and no19-gate counterexample was found.
