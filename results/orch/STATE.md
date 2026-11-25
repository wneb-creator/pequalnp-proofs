# Continuing state

This is an ongoing attempt on **L-meta-2448**. The posted theorem is **not proved**. Do not open a proof PR for the current partial file.

- Repository: `/workspace/pequalnp-proofs`; authorized branch `pnp/pilot-75`; only push to fork `origin`.
- Job began 2026-11-25 07:02:59 UTC. Lease obtained 07:04:37 UTC. Continue sustained work; do not stop merely because partials compile. Ninety minutes from job start is 08:32:59 UTC.
- Exact gap and statement: `/tmp/oec/pequalnp-pilot-75/gap.json` and `statement.txt`.
- Only this job's lease is in `desk-first.json` in the same scratch directory. Never display its identifier or touch other pilots' leases.
- Root heartbeat runs every eight minutes (PID tracked in scratch heartbeat.pid; restarted as13568); logs are `heartbeat-process.log` and `heartbeat.log`. Manual renewals before long operations use curl exactly as join.txt specifies. Append/summarize sanitized responses into `desk-log.txt`; no null answers so far.
- Lean: prepend `/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux/bin` to PATH. Full pinned cache downloaded successfully. Never lake update or build Mathlib from source.
- Checker requires `PEQUALNP_REAL_LAKE` set to the explicit lake binary above, and `PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-75/build-state` for its queue.
- Last pushed checkpoint at this note: `5ec0e88f61eba2f9044c9d3159fc97e91af7ea93`. The named file has 1969 lines and its build passed; the existing local checker verdict is `REJECTED (no-theorem)` because the main declaration is absent.
- Fourteen exposed partial lemmas were checked for axioms: only propext, Classical.choice and Quot.sound; complete output is scratch `partial-axioms.log`.

## Active team

Six sub-agents have been used (do not count root): status_review, structural_proof, library_route, finite_cases, lean_setup, global_normal_form.

- status_review independently reviews each compiled Lean fragment before root pushes it. It has reviewed the broader frozen OneJunkTopFree and EarliestJunk prototypes.
- library_route compiled a new conditional one-junk, singleton-silent graph-cover bound without a bipartite assumption. This prototype imports checked L_meta_3760 and must remain a results artifact until dependencies are extracted. Full target allows multiple interacting dirty gates.
- global_normal_form has frozen, reviewed component extraction already integrated; now formalizing continuation/suffix interfaces in fresh files.
- structural_proof's equal-size star-prefix repair is integrated; it is investigating separate AND/OR lower bounds or another full-goal invariant.
- finite_cases runs exact finite circuit synthesis. Basic CNF encoding independently reviewed by lean_setup; solver UNSAT is computational evidence, not a Lean proof. Theta 233/333 900-second SAT runs were still active near 07:38 UTC. Many heuristic searches found no counterexample.
- lean_setup also independently reviewed finite artifacts and all 1197 logged BFS witnesses. It can review additional computational artifacts.

## Publication constraints

The user explicitly requires early preservation of compiled partials on the work branch, including results artifacts. This is why the branch currently adds more than one file. An actual proof PR must have only the named Lean file in its final diff; preserve results in earlier branch history if such a PR becomes possible. No PR yet.

Before every push: independent review, meaningful build, stage named files, git status, explicit commit. Print PUSHED with branch, SHA, gap, and honest description. Never claim checker acceptance for a partial.

At completion include `Sub-agents: ...`, `TIMING total=<minutes> subagents=6`, message-id acknowledgement, null count, and finish with the exact three lines for gap, PR, checker verdict. Release only this lease. Do not lose checked work.
