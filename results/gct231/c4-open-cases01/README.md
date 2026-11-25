# Four checked scalar contradictions for C4 open cases 0 and 1

**Lean PASS**, exit 0 in 190.063 seconds, peak sampled process-group RSS 4,792,816 KiB. The final source is `C4OpenCases01Scoped.lean`, SHA256 `7944028ae577f616c88a4ba2f76717c5812c9a5fc480b73199b519797296401b`, 124,858 bytes / 134 lines. Its exact-source audit reports only propext, Classical.choice, and Quot.sound for all four theorems. Complete output includes harmless tactic-sequencing linter warnings.

The source preserves the two independently checked case0 certificate bodies and derives case1 by substituting gamma -> -gamma. The exact necessary equations transform with signs (+,+,+,+) for the zero branch and (+,-,+,-) for the nonzero branch. The latter proof uses only generators 0,1,3, so its wrapper has precisely those three equation premises and the open-factor premise. Both heartbeat and recursion limits are scoped with `in` above each theorem; the sole import is PEqualNP.Defs.

Independent reviews are copied unchanged in `c4_compressed_review/` and `c4_scoped_review/`. They verify the exact certificate identities, source premises, final square-removal identities, sign substitution, body preservation, argument counts, and format. Underlying exact inputs, traces, replayed certificates, and geometric/resultant reviews are preserved in sibling `c4-open0-zero/` and `c4-open0-nonzero/` archives.

These theorems prove four explicit scalar polynomial-system contradictions used in open fixed-C4 support cases. They are **not** the full C4 geometric theorem or the posted gap. No new axioms, sorry, native_decide, prohibited root text, or string literals occur in the final source.

The separate `failed-prior-candidate/` directory preserves the earlier failed combined source and complete diagnostics. Its nonzero wrapper incorrectly referred to unused h2; it also used scratch-only global options. It is not a checked theorem artifact. The final source removes that stale bullet and scopes the options. The failed candidate's audit output must not be interpreted as a valid proof.
