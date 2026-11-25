# L-meta-1031 research checkpoint

The assigned theorem remains unresolved. No proof PR has been opened. The named Lean file is a **conditional partial**, and the repository checker rejects it because the unconditional named theorem is missing.

- `../../lean/PEqualNP/Outside/L_meta_1031.lean` is the conditional one-unsound-AND result: from an existing globally least public circuit with normalized AO2 form and exactly one unsound AND, it derives the exact requested existential star-ownership conclusion. The source is 9,791 lines / 497,881 bytes after deletion-only simplification.
- `partial-build.log` records the successful named-file build. `checker-latest.log` records the actual rejection on that same compact file.
- `lemmas/FreshBudget.lean` proves a general circuit exchange deleting one gate and all its direct readers, then adding sound stars. To eliminate an unsound AND using it, a sufficiently cheap pivotal-edge star cover is still needed.
- `lemmas/FreshCore.lean` supplies concrete one-slot replacement criteria and preservation of earlier raw ownership. `FreshMixed.lean` gives local two/four-gate filtering lower bounds. `FreshGroups.lean` constructs grouped two-star corrections with exact cost.
- `lemmas/P5Exchange.lean` and `P5Context.lean` preserve three shared OR ports while replacing a ten-gate path block by eight gates; private old ports are explicitly excluded from the contextual theorem.
- `lemmas/PetersenOrCounterexample.lean` is a kernel-checked counterexample to the auxiliary unconditional OR-count conjecture: ten graph edges, no triangles/four-cycles, eight ORs and six ANDs. It does **not** refute the assigned theorem: a thirteen-gate star circuit exists, and an existing library theorem establishes the corresponding total lower bound.
- `lemmas/OrPotentialBoundary.lean` disproves a simpler component-merging invariant. `ProfileVersusSound.lean` distinguishes star ownership from all-AND semantic soundness using an explicitly nonleast example.

Independent source reviews and axiom-audit outputs are retained alongside the artifacts. The accepted partials use only the standard Lean axioms (propext, Classical.choice, Quot.sound, or subsets). Numerical SAT/MILP evidence is separately labeled; a timeout is inconclusive. Large native proof traces are kept in scratch during the job, while small CNFs, outputs, verification logs, hashes and reproducible sources are retained here.

The initial desk assignment reported all three reduction slots occupied, so a fourth reduction was not submitted. Only the root holds and renews the L-meta-1031 lease. See `TIMELINE.md`, `NOTES.md`, and `validation.txt` for measurements and chronological findings.

Final checked extensions: `FirstLiteral.lean` preserves all existing gate ownership while normalizing an already-owned first star under its explicit prefix and degree premises; `FreshTheta.lean` proves a concrete equal-size theta-template rewrite; `FreshBridgeFactors.lean` classifies three-bridge families under explicit Branch premises. Their source reviews and axiom audit logs are included. None supplies the remaining unconditional global argument.

The two final total-gate SAT searches (Petersen minus one vertex with 15 gates, Petersen with 19 gates) each returned `c UNKNOWN` at 900 seconds. `native-total-final-verdicts.json` records the exact outcomes. Drafts in `experiments/` are explicitly unverified and are not accepted Lean results.
