# Lower-bound preservation status

Development stopped after the root reported HTTP 410. No proof build remains active.

The self-contained `lower_bound_binary17_checked.lean` compiled successfully (exit 0) and independently passed source review at SHA256 `c9f474e6ab6295325381d345b003a63b90c487e8f70bcf213671cf62679c8843`. It proves an unconditional Petersen lower bound of 17 binary gates, equivalently 17 + NOT count <= circuit size. Consequently any size <= 19 counterexample to L-meta-2592 must have exactly one or two NOT gates. This is a checked partial result, not a proof of the posted gap.

Complete build, integration, and axiom-audit stdout/stderr are preserved in `results/orch/validation/`. The axiom audit reports only propext, Classical.choice, and Quot.sound. The full build has 37,389 bytes of warning-only stdout and empty stderr.

The import-based integration file is also checked, but depends on local modules reconstructed from existing_binary17_base.lean, lower_bound_pair_symmetry.lean, and lower_bound_row_encoding.lean. The self-contained checked file has no such local-module dependency.

`lower_bound_double_zero_snippet.lean` is an unfinished draft. Its last already-running test finished with Lean errors; no correction or new build was attempted after the stop. Full failed diagnostics are preserved as lower_bound_double_zero.stdout and .stderr. Its intended next argument projects two pins to zero, using signed residual floors 13/12 and three/four live constant roots, but the projection argument is not established by this draft.
