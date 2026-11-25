# Independent forced semantics review

Core: `results/orch/lemmas/ForcedSemanticsCore.lean`, 463 lines, SHA256 `25172452539830f7588eb1da3948504db80fa0801fa768b4c61f9fa3d42b68b5`.
Full: `results/orch/lemmas/ForcedSemantics.lean`, 720 lines, SHA256 `20c198cd41bd64f4b3d44b37ff2454ab745d50feb219b01f54b346c2c023cdb3`.

Source review: PASS. No semantic or formatting defects found. Both files retain frozen PruningCore as an exact prefix. The full file adds the same OR-closure recursion already independently inspected in MaskingNext, followed by forced evaluator input and gate equations and OR-path propagation.

SemLE requires equal list lengths, so the forced-gate position is synchronized when comparing evaluations. AND/OR monotonicity uses the actual gate evaluator and false-default wire reads. The forced evaluator is pointwise below the original evaluator for arbitrary input lists. Its equality when the original q-wire is false is proved by reverse induction on gate lists, and does not silently require q to be valid: missing reads are handled by the false default. The pruned evaluation wrappers carry the required input-length and IsAO2 assumptions from the compiler equivalence.

The full gate recurrence explicitly requires a valid k and ReadsBack. For OR propagation, the designated forced gate must be an AND; each traversed OR is proved different from q before its ordinary evaluator equation is used. Input OR reach is extracted using the correct DecidablePred instance, and input wires stay unchanged. Thus the final OR-input propagation conclusion is on all Boolean inputs and does not rely on testing edge pairs.

These are evaluator/compiler components only. They do not prove the whole target or automatically show that pruning preserves the target graph function.

Format scan: only Mathlib and PEqualNP.Defs imports; no forbidden tokens, new axioms, attributes, options, or execution commands in the reviewed Lean source.

Independent core rebuild: PASS, exit 0 without warnings. Axiom audits of forcedValues_mono_input, forcedValues_agrees, pruned_eval_below, and pruned_eval_agrees use exactly propext, Classical.choice, Quot.sound. Full output: `forced-semantics-core-independent-audit.log`.

Independent full rebuild: PASS, exit 0. Two harmless if_neg deprecation warnings. Axiom audits of forced_gate, forced_orReaches_true, and forced_orIn_true use exactly propext, Classical.choice, Quot.sound. Complete output retained in `forced-semantics-independent-audit.log`; audit source is ForcedSemanticsIndependentAudit.lean.
