# Mathematical interface review: selected dirty paths

Reviewed by constructive on 2026-11-25 UTC. Source: `/tmp/oec/pequalnp-pilot-70/lower-bound/SelectedDirtyPaths.lean`. Read the complete appended diff against the previously checked `TwoPathFork.lean`.

Status: mathematical interface PASS; UNCOMPILED. Cache recovery is pending, so neither the author nor this reviewer has a completed Lean check for this extension. This is not a build-success verdict.

Final-status update, 2026-11-25 UTC: the final 164-line `SelectedDirtyPaths.lean` subsequently completed Lean with author-reported exit 0 and an empty `selected-dirty-paths-lean.log`. Its SHA256 is `77ccf0da4bc6d6e05f2d81f822b2a812bec2c1b06b9044bb798c5072e2022190`. Repo_review independently reviewed that final checked source; see `selected-graph-paths-review.md`. The uncompiled status above records the earlier interface review and is superseded by this completed check and final review.

The selected-path induction correctly uses an earlier selected D=true child to reach d. Prepending a D=false clean consumer leaves all positive-index path vertices D=true, which supplies the cross-start exclusions needed by the checked two-path fork theorem.

The maximal-live-D argument needs no unspoken root-subset condition: a maximal D=true live vertex cannot be a root because roots are D=false. Its live parent is larger by the explicit child-index condition and hence cannot be D=true, giving the desired clean transition. Finiteness is supplied by V.

The final path-flag lemma proves an arbitrary adjacent false-to-true transition from a false start and true endpoint. That is enough for semantic escape: after verifying that the pair hits both raw supports at d, any D=true wire accepts that raw pair through its OR-only connection to d. The selected clean consumer's opposite operand accepts by AND semantics, irrespective of which later accepting branch the path follows. Therefore a last-transition lemma is unnecessary.
