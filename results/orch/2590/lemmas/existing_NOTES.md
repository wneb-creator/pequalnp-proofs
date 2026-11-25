# Existing-results work for L-meta-2590

2026-11-25 15:24 UTC. Only the current gap is being developed.

- `existing_mono9_full.lean`: full checked upstream L_meta_4033 source renamed into `PEqualNP.Outside.L_meta_2590_aux.MonoNine`; its original final theorem is enclosed as `checkedOriginalNine`. Source frozen at SHA256 `10fdad82d2fddcbbc5c83739d1e7b622e10b8cb11d0574f707d748bad60268aa`, 521725 bytes, 6583 lines. Local recompile was INTERRUPTED by root instruction after the lease renewal failed. Exit status130; no .olean produced. This namespace adaptation has NOT been locally verified. Complete logs are `/tmp/oec/pequalnp-pilot-107/2590-existing-mono9-full-1.stdout` and `.stderr`; module `ExistingMonoNine` in scratch `leanmods`. Main exported target: `monoRoot : Impossible false graph 15 inputs.toFinset`, a pure-monotone nine-input floor of 16. It also contains the signed floor of 15 and original general-circuit floor of 16.
- `existing_mono9_core.lean`: FAILED lexical dependency extraction. It omitted dotted projection definitions and a mutual-block theorem. Do not use or claim it compiles. Complete failed log is `2590-existing-mono9-core-1.stdout/.stderr` in scratch.
- Actual Lean dependency pruning is assigned to status_1035 after the full module completes. Root and lower_bound have the exact namespace/interface. Four inherited structures KWRooms, FreeRooms, SingleFactor, PanelProof need pruning or product/subtype encoding for the automatic plain-file route if retained; CONTRIBUTING allows human review for own datatypes.

Useful checked upstream facts found:

- L_meta_4342 normalizes any Monotone2 circuit with false output on all-false input to an IsAO2 circuit of no larger size and identical function. Semantics agent owns adaptation.
- L_meta_584 gives an exact 20-gate Petersen witness with 13 OR and 7 AND gates, so a blanket 14-OR lower bound is false. L_meta_587 gives the standard 14-OR, 6-AND witness.
- L_meta_9781 excludes a monotone circuit of size at most 16 for Petersen with adjacent edges (0,1),(1,2) removed. It concerns exact graph semantics, not just edge/nonedge boundary rows.
- L_meta_1665 through L_meta_1678 exhaust the first-gate orbit types on the nine-vertex residual, but their total lower bound is only 16, not 17.
- R_meta_2590_1, R_meta_2590_932, R_meta_2590_491 all retain substantive unproved finite/normalization hypotheses; they do not settle the target.
- A census of existing Monotone2 and AO2/count-related final statements found no exact unconditional 19- or 20-gate Petersen lower bound. The stronger-looking free-OR first-gate theorems L_meta_5236/5238 require NOT counts and do not apply to the pure monotone case.

All diagnostic census text is retained in `/tmp/oec/pequalnp-pilot-107/2590-existing-*.txt`. Root handles leases, checker, independent review, git and submission. No desk or git actions were performed by this agent.

2026-11-25T15:25:50.916151+00:00 STOP: root reported lease renewal error. Build session97461 terminated with Ctrl-C, exit130. All full and failed-extract stdout/stderr copied to results/orch/2590/logs. No new proof development or build after stop. Fullsource remains frozen; no successful compilation is claimed.
