# Independent review: standalone assembly

UTC: 2026-11-25T17:50:57.390658+00:00

Verdict: assembly/source-format PASS at SHA-256 `5ceb73446dabfc7085ede651dd0b863bf362bf6fc51ad43eae156ff261f85923`. Named file: lean/PEqualNP/Outside/L_meta_9775.lean, 513,216 bytes, 7,441 lines, 11,072 bytes below the 512KiB limit. Root's standalone lake build is in progress; this review does not yet assert that build or checker succeeded.

All37 assembly inputs match their manifest byte counts and hashes. Independently reconstructing the output by removing only top-level import lines and normalizing outer whitespace reproduces the named file byte for byte. All ordinary components are otherwise verbatim. The selected PrivateProjection module is independently verified as the unchanged generic prefix, exactly13 requested theorem blocks with their scoped options, and the original closing namespace. No theorem body or finite witness was altered by selection.

The named file has exactly one import, PEqualNP.Defs. It contains exactly one fully named final theorem, the reviewed exact negation of the leased existence statement. No prohibited proof markers, root-name text, strings, initialization, or attributes other than simp were found; every option is a locally scoped member of the four-limit allowlist.

The complete modular wrapper and its semantic dependencies have independent reviews. Certificate payloads are audited separately against the frozen packed-source manifests; the final standalone build will kernel-check those actual inlined payloads. Final axiom audit, exact-statement refutation checker, and one-added-file PR diff remain required after this source assembly review.
