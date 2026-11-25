# Read-only pruning analysis for both nine-variable certificates

UTC: 2026-11-25T16:03:11.862365+00:00. No proof source was edited or new build run for this analysis.

Checked source L_meta_4332 is 520393 bytes. To retain both monoRoot and signedRoot while replacing its standard-Circuit bridge, the following original inclusive line ranges have no retained Circuit-symbol dependencies and can be omitted: 123–133, 225–272, 307–367, 760–765, 6128–6192, and 6865–6977. The result before a restored closing namespace is 505102 bytes, leaving 19186 bytes under 512 KiB. This is a textual dependency audit, not a compiled pruning result.

Keep pull_gate at273–306: reach_live_sub uses it at697. Keep represented/Repr, bin_rep, prime_rep, and their supporting normalization lemmas: the Reach-to-Live conversion uses them. Do not delete the entire first350-line block.

Two additional isolated unused declarations can be removed: neg_laws146–147 (86 bytes) and lower_forest2341–2352 (703 bytes). That leaves504313 bytes and19975 bytes of nominal helper room. The apparent zero references to Forest.* and BoundPool.* definitions are a lexical false positive: those fields are used through dot notation and must remain. Both roots, requiredInputs, graph_proper, edge_table, and sampled are needed by the intended semantic bridge. Restore the closing namespace after dropping the old final wrapper.

All listed ranges and symbol occurrences were checked against the existing source, but only a fresh Lean build can establish the complete pruned module. No conversion of long decimal literals is available as a space optimization: the large certificate data already uses hexadecimal with no redundant leading zeros.
