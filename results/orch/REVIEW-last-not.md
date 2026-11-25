# Independent review: last-NOT checkpoint

Reviewed UTC: 2026-11-25T14:09:04.062872+00:00
Reviewer: lean_setup (independent of proof author)
Verdict: PASS for preservation push of partial result; NOT a complete proof submission.

SHA256 (both LastNot.lean and lean/PEqualNP/Outside/L_meta_2592.lean): 883ecbfc0ca4555946afdf1144751627134546dba9d1c14255a8253ce4d16902
Lines: 81

- The target is byte-for-byte identical to the reviewed helper file.
- Last-NOT splitting, gate-count identity, preserved wire indices, and suffix monotonicity match the library semantics. The empty NOT-input case correctly uses the out-of-range false wire at n + pre.length; subsequent gates preserve original indices because Q receives all prefix wires plus the NOT output.
- Only PEqualNP.Defs is used. All three helper lemmas are inside the permitted module namespace. No forbidden commands, axioms, placeholders, root qualifier, strings, attributes, options, custom types, or instances are present.
- Compilation was reported by root as exit 0 with empty stdout/stderr; this reviewer did not rerun the build.
- validation.txt clearly records PARTIAL ONLY and that the posted theorem is absent and its checker has not run.
- Checked validation.txt, NOTES.md, and TIMELINE.md for token/private-key patterns: none found.

The final proof PR remains blocked until the exact posted theorem and successful local checker verdict exist, and its diff must add exactly one Lean file. Results files are checkpoint evidence on the working branch only.
