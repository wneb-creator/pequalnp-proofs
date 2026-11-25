# Independent OneJunk review

Reviewed frozen extension `results/orch/lemmas/OneJunk.lean` (295 lines, SHA256 `392e1c5c6d944a974612e8644405785387a1f0e6b60da416c39bd60ae709e65a`) and assembly `OneJunkAssembly-frozen.lean` (790 lines, SHA256 `bf0227b32056fe7b420e013d98646ce4ccc57c7fd48555921685ebe3f631b87b`). The assembly contains the exact extension after the two import lines.

Source review: PASS. No defects found.

The cone recursion uses the actual library filter for earlier gate wires, proves strict index decrease even without ReadsBack, and requires real-gate and backward-input bounds when lifting an operand into an AND cone. TopForm is used with its exact library meaning: a BelowF AND cannot occur strictly below another AND. Together with the unique-junk hypothesis, this makes every AND source of an AND operand the designated q. The designated q cannot reach itself through an earlier operand; hence its operands have pure OR-input semantics. For a productive reader, reaching q on both sides would make q BelowF, contradicting the dirty hypothesis. Splitting the two Fin 2 cases gives the exact claimed reader expression for every Boolean assignment, not merely edge pairs.

Missing/out-of-range gate behavior is not assumed away: all semantic reader gates and q carry explicit real-gate bounds; operand validity follows IsAO2. The nonempty-side conclusion uses dirty q to obtain a true valuation and then the proved junk expression.

The result remains conditional on TopForm, IsAO2, and at most one non-BelowF AND. It does not establish these hypotheses for a general circuit or prove the posted gap.

Formatting review: only Mathlib and PEqualNP.Defs imports; no forbidden token, string, new axiom, attribute, option, or execution command in the frozen assembly.

Independent compilation and axiom audit: PASS, Lean exit 0. Only the inherited MaskingNext unnecessarySimpa warning at line 16. Printed axioms for productive_reader_semantics, junk_sides_nonempty, and inCone_lt are exactly propext, Classical.choice, Quot.sound. Complete output retained in `one-junk-independent-audit.log`; audit source is `OneJunkIndependentAudit.lean`.
