# L-meta-2592 partial handoff

The exact posted theorem is not proved. No proof PR was opened. The named file contains checked helper lemmas, not the final theorem.

## Strongest integrated result

`lean/PEqualNP/Outside/L_meta_2592.lean` proves `seventeen_binary`: every FanInTwo Petersen circuit has at least17 non-NOT gates. Hence `three_not_impossible` excludes size-at-most19 circuits with at least3 NOTs. The named module built successfully with5149 jobs; complete stdout/stderr are in this folder. The source has5067 lines and307671 bytes; SHA256 `f732b81f0ff72689f36fb158e090dcd52455ac0e2911211c9b9357d9738334dc`.

The full-gap local checker was not run because the exact final theorem is absent. No cleanup pass was attempted; the final integrated source stayed5067 lines before and after preservation.

## Further checked components

The lemmas folder preserves checked restrictions, first-gate and prefix bounds, terminal-NOT elimination, distinct and repeated terminal-NOT-child cases, a compiler for semantically constant NOT gates, and a C6 lower bound with supplied opposite-pair ORs. `review-checkpoint.txt` states each component's precise assumptions and provenance. Some light development tests explicitly assume a separately checked certificate to avoid recompiling it; these assumptions are not theorems of the full gap.

Remaining cases have one or two internal nonconstant NOTs and an AND/OR output. The terminal-output reductions become useful after an unconditional monotone Petersen floor18 is integrated. The JointReadable certificate core in `lemmas/unfinished` completed Lean successfully at14:43:55 UTC after19m18s. It proves the unconditional nine-input monotone floor16 and signed floor15, plus the generic extraction bridge. Its532411 bytes exceed the512KiB submission limit. The later combined mono18 assembly remains unchecked, and the compact variants have known syntax errors; the archive README distinguishes these statuses.

No19-gate counterexample was found. A known20-gate circuit was Lean checked. Search sources, all logs, candidate verifiers and hash manifests are preserved; heuristic failures and restricted SAT UNSAT results are not lower-bound proofs.

## Lease interruption

At14:33 UTC the desk renewed this pilot's lease to14:53. At14:38 it returned HTTP410: `no such live lease: it expired or was released. Ask /desk/next again.` The exact response with headers and full desk log are preserved. Checked components were pushed before recovery.

Two recovery requests with `another=1&hard=1` returned L-meta-2583 with the same lease issued at13:59, before recovery, and the note `you hold 5 gaps, the most one handle may hold at once; release one to get another`. That pre-existing lease was treated as another pilot's lease. It was not worked, renewed or released. Desk null count:0. New work stopped under the user's explicit lease-isolation rule, despite the remaining wall-time budget.

L-meta-1035 was already refuted via its negated twin L-meta-1036 in merged upstream PR2095; no work on it was attempted.

## Reproduction

Pinned Lean4.36.0 is installed under `/tmp/oec/pequalnp-pilot-95/toolchain/lean-4.36.0-linux/bin`. The official Mathlib cache was downloaded successfully, and Mathlib was not built from source. No `lake update` was run. The scratch toolchain is not part of this branch; use the repository's pinned toolchain on another machine.

This is a preservation branch with result artifacts, not a PR-ready single-file branch. A future full proof PR must add exactly the one named file and no results artifacts. Only `pnp/pilot-95` was pushed to the fork remote origin.

Sub-agents: proof route; NOT cases; reductions; counterexample; SAT/CEGIS child; independent status/review/setup.
