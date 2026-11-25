# Operational state

Job: pequalnp-pilot-144. Work branch: `pnp/pilot-144`; push only to fork remote `origin`. No PR has been opened. Upstream base fetched during setup: `fdbd39a7`.

Start for timing: 2026-11-25 14:53:15 UTC. Ninety minutes is 16:23:15 UTC; approximate six-hour job deadline is 20:53:15 UTC.

## Desk

This job owns **no live lease**. L-meta-2583 and then L-meta-2590 both returned HTTP410 before the last expiry reported by their renewals. No release was called. Their full responses are preserved under `logs/`.

Recovery requests at 15:27:04, 15:31:43 and 15:36:00 UTC returned `gap:null` because the proof checker queue was backlogged. Null count: 3. The poller stopped after the 15:40:01 response returned L-meta-4970, whose lease had already been issued at 15:22:04.914 UTC. One permitted retry returned that same existing lease. Both responses said: `you hold 5 gaps, the most one handle may hold at once; release one to get another`.

The explicit other-pilot ownership rule requires stopping. Do not make more desk calls, work on L-meta-4970, send its beat, or release it. All proof and search agents are paused. No release was called. The original L-meta-2583 response is also retrospectively ownership-ambiguous; see README.md. L-meta-2590 is the last freshly issued lease this job held. No complete proof was obtained, so no proof PR can be opened.

## Toolchain and cache

The claimed prepared installation was absent. Root and repo_recon installed pinned Lean4.36.0 under:

`/tmp/oec/pequalnp-pilot-144/toolchain/lean-4.36.0-linux/`

Use its `bin/lake`, prepend its `bin` directory to PATH, and set:

- `PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-144/build-home`
- `MATHLIB_CACHE_DIR=/tmp/oec/pequalnp-pilot-144/mathlib-cache`
- `LAKE_ARTIFACT_CACHE=false`

Run commands from the explicit repository or `lean/` working directory. Never run `lake update`; never build Mathlib from source. A targeted cache and `PEqualNP.Defs` were built. Full Mathlib cache preparation stopped at closeout after seven successful bounded download batches, reaching 5,084 of 8,712 modules. The full Mathlib umbrella was never available, so this does not change the checker fault.

Safe environment closeout completed at 15:45 UTC. All 5,335 migrated immutable toolchain/cache files (3,758,096,332 bytes) were restored to regular disk files, with original hashes, modes and modification times verified. Both memory-file managers, PIDs 10297 and 12834, were terminated only after verification and no longer exist. No proof source was ever in anonymous memory. The filesystem mount attempt was denied and stopped; ordinary file I/O was used for the later memory-file prototype and restoration.

To make room for restoration, only identified post-baseline generated Mathlib cache additions and the disposable verified backup archives were removed. The original dependency closure remains: 2,547 of 8,712 Mathlib modules, and no full Mathlib umbrella. Final disk reserve was 560,832,512 bytes and available RAM was 9,362,820 KiB. The final `lake build --no-build +PEqualNP.Outside.L_meta_2590 +PEqualNP.Defs checklemma` preflight passed: `All targets up-to-date (5153 jobs).` Complete setup, cache-batch, restoration and capacity records are under `logs/environment/`; pinned-download fallback and restoration details are in its `memfd-cache/RESTORE.md`. No new proof validation is claimed by this environment preflight.

## Proof coordination

Six sub-agents have been used: repo_recon, structural_proof, structural_proof/dirty_blocks, counterexample, lemma_search, sat_search. Reusing these agents does not increase the count.

- structural_proof owns the single-read compression argument.
- counterexample owns normalization, pruning and deletion/prefix helpers.
- lemma_search owns Petersen input renaming/vertex symmetry.
- dirty_blocks owns OR/AND semantic restrictions and the9-input lower-bound transfer.
- sat_search owns constraint searches; interrupted runs have no verdict.
- repo_recon owns independent reviews and cache setup.

The exact compression child statement L-meta-7889 is recorded, but that child has never been leased. Existing components do not yet prove it. Any future child submission requires a proper lease and the exact checked statement. The current L-meta-2590 already has three live reductions; do not add a fourth.

Special-task correction: L-meta-1035 is already refuted by checked L-meta-1036 (an existentially normalized negation), despite its own row still saying conjecture. Existing source is lean/PEqualNP/Outside/L_meta_1036.lean. No work or lease was taken for it. Also L-meta-1508 already has checked negation L-meta-1507, so it is not a useful new target.

## Delivery

Checked components and all search evidence were pushed through commit `b32a0e8347d069b4e1b2bd5290220f330c76ee34`. The final closeout checkpoint preserves the remaining desk logs and these operational notes. The named partial files are not full proofs and have no final posted theorem. See README.md and validation.txt for precise claims.

Before any future push, obtain an independent review. Preserve compiled results promptly, printing `PUSHED <branch> <sha> <gap> <what>`. A proof PR must ultimately add exactly one allowed Lean file; artifacts can remain in branch history while the final PR diff is cleaned. Include final sub-agent and timing lines in the PR body and final response. The final response must end with gap, PR and checker verdict lines and acknowledge KIT-MESSAGE-ID msg-dff04cd5f8d997249819b16b.
