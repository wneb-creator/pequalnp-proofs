# Job pequalnp-pilot-134 preservation report

KIT-MESSAGE-ID: msg-b452a0a188b2b4977883c3ff
Status: stopped because desk returned another pilot's existing lease twice. No complete proof or refutation. No PR opened.
Own gap: L-meta-1890. Own lease was issued 2026-11-25T14:39:23.369Z; beat013 promised expiry15:38:49.079Z, but beat014 returned HTTP410 at15:25:16Z. Its full headers and body are preserved in beat-014-error-response.txt.

The specific HTTP410 recovery instruction was followed after pushing partials. Three recovery polls returned gap null. The next request and single allowed retry both returned L-meta-4970 with a lease issued15:22:04.914Z, before either request, and the exact note:

> you hold 5 gaps, the most one handle may hold at once; release one to get another

That lease belongs to another pilot. It was not worked on, renewed through its beat endpoint, or released. No further desk requests were made. The already-revoked own lease could not be released. All owned build/search/poll processes have stopped.

## Checked work

Named file: lean/PEqualNP/Outside/L_meta_1890.lean,124 lines. It proves missing-input counterexamples and size-preserving input relabeling; it does not contain the exact final posted theorem.

Command: lake build PEqualNP.Outside.L_meta_1890
Exit:0
Output: Build completed successfully (5149 jobs).
Complete output: build-partial-004.txt.

Local checker: not run against the posted statement because its final theorem is absent. No checker acceptance is claimed. Cleanup was skipped because no complete proof/checker pass was obtained; named-file line count before/after cleanup:124/124.

Additional checked helpers and their full compiler outputs are recorded in validation.txt and adjacent validation files. SignedBounds.lean is an independently reviewed unconditional ordinary-nine lower bound15. It is not a proof of gap1890. The stronger Bounds.lean check was interrupted with exit143 and no verdict; full output and identifier map preserved. Failed drafts remain explicitly marked unverified. All SAT/exhaustive searches were unfinished and found no counterexample; no UNSAT result is claimed. Valid v2 exploratory checkpoints and complete logs are archived with hashes; invalid earlier checkpoints are excluded and identified.

Independent reviews covered the named-file proof, each checked helper, source restrictions, and preservation-only drafts. All commits/pushes went only to origin pnp/pilot-134. No PR/issue/comment was created.

## Desk null responses

Null count:3. Exact messages, in order:

> The checker is behind: 521 proofs are queued for a check and 528 were checked in the last hour, about 59 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

> The checker is behind: 521 proofs are queued for a check and 516 were checked in the last hour, about 61 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

> The checker is behind: 521 proofs are queued for a check and 486 were checked in the last hour, about 64 minutes of queue. No new proof work is handed out until it catches up. A step you already hold a proof of can still be leased with &gap=<id>&have=proof.

Full timestamped desk transcript: desk-log.txt.

Sub-agents: status_review, toolchain, structural_proof, counterexample, finite_certificate, readtwice, finite_certificate/search_audit
TIMING total=65.3 subagents=7

Report UTC:2026-11-25T15:41:51.815470+00:00
