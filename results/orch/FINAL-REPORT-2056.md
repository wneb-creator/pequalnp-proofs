# L-meta-2056 final report

No complete proof or refutation was found. The posted statement asks for a monotone binary circuit with at most63 gates for the26-input order-three projective-plane incidence function. The checked baseline has64 gates. The unresolved case permits multiple dirty intermediate AND gates.

The named file lean/PEqualNP/Outside/L_meta_2056.lean is a728-line partial verifier plus64-gate control. `lake build PEqualNP.Outside.L_meta_2056` passed with `Build completed successfully (5149jobs)`. Its exact posted theorem is absent. The target checker was not run to acceptance, no final cleanup pass was attempted, and no PR was opened. Named file lines before/after cleanup:728/728 (no cleanup). Complete build output is preserved in named-2056-partial-build.stdout and .stderr.

The strongest new helper, TwoDirtyNecessary2056.lean (6865lines), compiled successfully in134.637seconds and passed independent review. It requires full correctness and explicit normalization hypotheses: monotone binary gates, lift fixed point, every gate live, and no clean wire used as an AND operand. Under those assumptions, size at most63 implies two distinct dirty AND gates. It has no singleton-rejection premise. It neither constructs a63-gate circuit nor rules out all such circuits. Complete stdout, stderr and resources are preserved in two-dirty-necessary-2056-build.*. OneDirtyPlane2056 and SumPlaneReadOne2056 give weaker restricted bounds. Existing L_meta_1898 was locally rebuilt successfully and supplies a13-AND lower bound for the equivalent difference-labeled plane; the new transport helper keeps that bound as an explicit premise. AllCleanBudget2056 is an extracted source not separately compiled; its complete body was kernel-checked inside the combined TwoDirty module.

All final searches finished before20:00UTC:

| Search | Configured native limit | Outcome |
| --- | ---: | --- |
| K13 bounded-cost encoding |2400s|UNKNOWN; no model|
| ComponentV5 finite grammar |2400s|UNKNOWN; no model|
| K16 bounded-cost encoding |2400s|UNKNOWN; no model|
| Full63 two-dirty encoding |1320s|UNKNOWN; no model|
| Same full63 formula, nested warm phase |480s|UNKNOWN; no model|
| General exact local optimizer, six seeds |598s|No63 candidate; best65 Read1, best nonRead1_66|

Complete native and wrapper diagnostics, source/data hashes, models when produced, independent reviews, and recovery evidence are retained. The environment transition left several wrappers terminated while their native children continued. Their causes are not established; missing original parent wait results remain explicitly unavailable. Kernel zombie wait statuses, native shutdown logs and posthoc recovery are distinguished from original wrapper observation. The last nested query completed with both native and wrapper exit0 and both reaped. The local optimizer recorded75 distinct correct circuits, independently checked on756 boundary rows; its two best representatives were also checked on all67,108,864 inputs.

These outcomes are not nonexistence proofs. The earlier full AND13 query was intentionally interrupted when the stronger compiled two-dirty condition became available. The old12-AND query was stopped because existing L1898 rules out that configuration, not because SAT proved UNSAT. Restricted grammar or membership-cost searches do not establish an unrestricted circuit lower bound.

The final narrow upstream check at19:52:53UTC found no exact main L_meta_2056.lean and no open PR matching2056 in a completely paginated search. This is a timestamped narrow check, not a claim about all related work. Full API responses and repository identity are preserved in research/final-upstream2056.

The job began2026-11-25T14:15:09UTC. Three earlier assignments returned HTTP410 before their advertised expiry times; the cause was not established, and this job did not release them. Complete required410 diagnostics are preserved. Before the current assignment there were three null desk answers; exact message text and UTC timestamps are in null-polls-2056.json. Only root controls the current L-meta-2056 lease. It will be released with reason out_of_time after this reviewed checkpoint is pushed; a separate release receipt will record the actual outcome.

Sub-agents: circuit_search, gate_elimination, not_elimination, proof_route, status_review, toolchain_setup
Acknowledged: msg-61f9b55d28c5586ddb66ac34

Report frozen at 2026-11-25T19:59:41.891270+00:00
TIMING total=344.55 subagents=6
