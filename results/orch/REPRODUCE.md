Checked supporting results for L-meta-2592

These are partial results. The exact posted theorem has not been proved, and no proof PR has been opened.

Use the repository-pinned Lean toolchain and run `lake exe cache get` from `lean/` first. Never update the pinned dependencies.

The named file contains Binary17 and Binary18 inline. Build it with `lake build PEqualNP.Outside.L_meta_2592` from `lean/`. It proves a seventeen-plus-NOT lower bound and a restricted eighteen-binary bound.

To include the separately checked FirstOr consequence in one standalone source, concatenate `results/orch/lemmas/Binary17.lean`, `Binary18.lean`, and `FirstOr.lean` in that order. Only Binary17 has imports; each snippet closes its own namespace. Run Lean on the combined file within the project environment. FirstOr concerns the normalized signed derivation, not the original circuit first gate.

Other standalone sources in the lemmas folder document finite graph facts, an explicit20-gate circuit, NOT-output exclusions, projection identities, and semantic NOT replacements. Partial.lean is the checked combined finite graph and upper-bound file; it does not depend on the snippets.

Full output and independent review records are stored alongside this note. The initial checker attempt faulted after an out-of-memory kill; a later isolated retry is planned.
