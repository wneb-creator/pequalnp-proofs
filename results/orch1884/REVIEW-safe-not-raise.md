# Independent review: SafeNotRaise

UTC: 2026-11-25T16:45:23.516417+00:00

Verdict: PASS. Source SHA256 `a85d2afe327c0048969aa42d6f14e73272b87aed04b31bf1eda10ea5ed2a1d58`, 5662 bytes/126 lines. Author reported Lean exit0; complete1884-safe-raise-001 stdout/stderr are empty. This reviewer did not rebuild.

The existing SafeNotReplacement body is byte-identical apart from trailing whitespace. replace_not_le adds the unconditional one-sided comparison: replacing the selected NOT output bytrue can only increase the final output when the suffix contains only AND/OR gates. The operand value may be arbitrary; its NOT is always≤true. replace_not_false requires the selected operand false, so old and new selected gate values are exactlytrue and the whole suffix receives identical banks; no suffix monotonicity is needed in this equality case. Both statements use the actual NOT headDfalse semantics and fixed gate positions, including arbitrary initial input lists and invalid references.

Only PEqualNP.Defs is imported, with the correct L_meta_1884.SafeNot namespace. No options, attributes, strings, forbidden constructs, new axioms, unsafe declarations, or secret-like content; below512KiB. These lemmas preserve or compare evaluation but do not delete gates or prove the row hypotheses needed by the main target.
