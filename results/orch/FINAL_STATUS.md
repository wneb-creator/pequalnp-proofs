# Final job status

Recorded 2026-11-25T15:45:44.660056+00:00. Job pequalnp-pilot-143, message msg-ac60831609e60df2b4f1f889.

No full posted theorem or refutation was established. No PR was opened. Compiled partials, complete diagnostics, and unverified research sources are preserved on branch pnp/pilot-143. This branch contains research archives and two partial files; it is not a compliant single-file proof PR.

## Compiled results

- lean/PEqualNP/Outside/L_meta_2583.lean: 2524 lines. The last named build passed: Build completed successfully (18423 jobs). Upper and lower bounds, incidence semantics, and conditional normalization were proved; unrestricted size-preserving ReadK normalization remains unresolved.
- lean/PEqualNP/Outside/L_meta_2590.lean: 46 lines. The named build passed: Build completed successfully (18423 jobs). Gate-count partition and conditional contradiction only; exclusion of all 19-gate Petersen circuits remains unresolved.
- Petersen readk_bound.lean proves the 20-gate lower bound with an extra ReadK1 assumption. library_rup.lean and library_profile.lean also compiled. These are components, not the posted theorem.
- normal_and6.lean and library_witness.lean are UNVERIFIED: their Lean runs were interrupted after lease failure. The explicit 20-gate witness was checked computationally on all 1024 inputs, but not Lean-checked. No minimum of 20 is claimed.

Local checker: the earlier 2276-line L-meta-2583 partial was REJECTED (no-theorem): no theorem named PEqualNP.Outside.L_meta_2583. The latest 2524-line source still has no final theorem. The checker was not rerun after that extension, and was not run on L-meta-2590. Neither file has checker acceptance. Full build and checker stdout/stderr are in the corresponding results/orch and results/orch/petersen files.

Cleanup: skipped because the full theorem/checker never passed. Named-file line counts before/after: L-meta-2583 2524/2524; L-meta-2590 46/46. No proof source changed during final archiving.

## Desk and stopping condition

The L-meta-2583 and L-meta-2590 renewals each returned HTTP 410 before the expiry most recently announced by the desk. Each received one diagnostic repeat with curl -si; complete headers and bodies are saved here. The cause is unknown. Neither lease was released by this job.

There were exactly four null responses: recovery request at 15:25:49 UTC and polls at 15:29:49, 15:33:49, and 15:37:50 UTC. Polls used curl -s and were spaced four minutes apart. All exact notes are preserved in final-desk/desk-log.txt and individual JSON responses. The last null note was:

> The checker is behind: 521 proofs are queued for a check and 487 were checked in the last hour, about 64 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

At 15:41:50 UTC, the desk returned L-meta-4970. One permitted retry with another=1&hard=1 returned the same gap and lease id. Both replies contained:

> you hold 5 gaps, the most one handle may hold at once; release one to get another

Both responses also had lease.terms.issued_at=2026-11-25T15:22:04.914Z, earlier than this job request. That nested terms timestamp is not conclusive proof of lease creation or another pilot ownership. Given the repeated lease and shared-handle warning, this job could not establish distinct ownership and stopped under the user existing-lease rule. No proof work, renewal, or release was performed on L-meta-4970. Polling exited after that assignment; no further desk request is scheduled.

The initial public checks did not find an accepted L-meta-1035 refutation; the desk assigned different gaps, so that special-case proof was not attempted. Later read-only comparison of preserved components with all 1588 public open-gap rows found no exact completed open statement to submit through have=proof.

## Measurement

Sub-agents: 7 total: status_audit (independent review), readk_strategy (construction and ReadK bounds), library_route (lower bounds, RUP and finite profile), counterexample (finite/SAT searches), normal_form (gate normal forms), toolchain_setup (Lean/cache), and delegated gate_count_theory (gate counts and witness).
TIMING total=53.45 subagents=7

No proof acceptance timestamp exists. This is a stopped research archive, not an accepted proof or refutation.
