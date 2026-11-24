# L-meta-2584 partial research result

Job: pequalnp-pilot-39. KIT-MESSAGE-ID msg-148a6e5d0fe0028d3bbca714.

The exact posted statement is unproved. No full-gap refutation was found.
No proof PR was opened. The public row did not enable reductions, so no
reduction was submitted. All results on this branch are partial evidence.

The central remaining obligation is a size-preserving global descent or
classification for arbitrary dirty AND chains and shared OR regions. The
checked local repairs do not establish that every circuit has an eligible
configuration. See global-route-assessment.md and pure-color-handoff.md.

## Preserved results

- Main helper file: lean/PEqualNP/Outside/L_meta_2584.lean.
  11186 lines; 512481 bytes; SHA256
  3d8e330ca362daf97df9e541cc1403a8a98b2fdb6cdcca15b922b912e165a6b2.
  It contains normalization, joint-read semantics, star constructions,
  structural restrictions, circuit rewiring, several complete conditional
  repairs, natural mixed-color elimination, and critical-edge purification.
- results/orch/lemmas/UpwardErase.lean: 154 lines, 7291 bytes; SHA256
  15160a5463e6cec975bf98aa0fe8e937122b01905156832550a012b97adee127.
  Exact strict gate deletion under all-assignment frontier guards.
- results/orch/lemmas/PureColorAlias.lean: 482 lines, 22491 bytes; SHA256
  4518980ee4ed024eef1f75894ea71ffe85ac16d1e1c18aca1a87dd3cb8d09805.
  Complete strict deletion for the stated pure three-point/one-line,
  two-dirty configuration, including shared uses. This standalone file
  includes the upward-erasure declarations; compile it separately from
  UpwardErase.lean. Neither standalone artifact is a proof PR source.
- finite-search/ preserves generators, queries, complete solver outputs,
  positive controls, and their manifest. These are computational evidence,
  not Lean proofs or a refutation of the posted statement.

## Validation

Pinned-toolchain lake build PEqualNP.Outside.L_meta_2584: exit 0.
Build completed successfully (18419 jobs).
Complete logs: build-018.stdout and build-018.stderr.
All 582 public helper declarations were audited; only propext,
Classical.choice, and Quot.sound occur. Complete axiom-audit-015 artifacts
and independent integration/format review-015-format.txt are preserved.
Independent component reviews and standalone compilation logs are beside
this report. These checks preserve the explicit conditional hypotheses.

Actual tools/check-lean.mjs on the frozen main file: exit 1.
REJECTED (no-theorem): the file declares no theorem named PEqualNP.Outside.L_meta_2584 (one lemma, one file: the theorem carries the module's name)
Complete logs: checker-partial-015.stdout and checker-partial-015.stderr.

Cleanup pass was not triggered: it requires both build and full checker
acceptance. Main-file line counts before/after cleanup: 11186 -> 11186.
No cleanup improvement or checker acceptance is claimed.

Desk null count: 0. Exact null message: none (the first request assigned
this gap). Full timestamped desk log remains in the requested scratch path.
The special L-meta-1035 task was checked initially but was not assigned to
this pilot. No other pilot's lease was used or released.

Sub-agents: 20 total across proof strategies, combinatorial and circuit
semantics, finite searches, toolchain recovery, and independent reviews
(including replacements after runtime restarts). Exact identities and
checkpoint timing are recorded in validation.txt and TIMELINE.md.
TIMING total=94 subagents=20

Own lease was released with reason `other` after pushing all checked results;
renewal timer stopped. Desk confirmation is saved in desk-release.json.
