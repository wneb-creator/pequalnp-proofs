# Historical research sources

The final checked source is `lean/PEqualNP/Outside/L_meta_3451.lean`. Its build and axiom audit are the validation target. These additional files preserve earlier work and are not separate proof submissions. Treat them as historical snapshots: after merging, an old wrapper importing the main module can redeclare names already present there. Validation uses the main source:

- `lemmas/global_prune.lean`: standalone verification wrapper for the pruning fragment, using copied monotonicity helpers.
- `lemmas/global_sensitive.lean` and `lemmas/global_sensitive_fragment.lean`: earlier sensitivity version, superseded by the stronger size-minimality version in the main file.
- `lemmas/global_sensitive_min.lean`: standalone verification wrapper importing the assembled main module.
- `lemmas/global_surgery_corollaries.lean`: earlier surgery source, superseded by `global_context.lean` and its assembled version.
- `lemmas/reduction.lean`: an unsubmitted, unvalidated reduction draft splitting singleton cleanup from subsequent pair cleanup. Its hypotheses have not been proved. The public step lacks the reduction flag, so this draft was not submitted or presented as a solution.
- `lemmas/singleton_strategy.md`: explanatory notes about the checked formula theorem and the unresolved shared-circuit extension.
- `lemmas/z3-proof-capability.stdout` and `.stderr`: complete solver capability diagnostics, not a Lean proof or proof-checker verdict.

No file in this archive establishes the unrestricted posted theorem. The stronger checked statements have been retained in the main source and indexed in `HANDOFF.md`.
