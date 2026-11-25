# Independent review of frozen PruningCore.lean

Reviewed 2026-11-25T17:35:59.032415+00:00 by lemma_inventory. Source: `/tmp/oec/pequalnp-pilot-161/PruningCore.lean`, 318 lines, SHA256 `f2ebe54370855e12bbb4917656d36856f96511c783a25dd1839a0039d55915d8`.

Verdict: no correctness issue found in the proved generic compiler semantics or AO2 validity. Suitable to checkpoint as a partial component; it is not the posted full theorem.

The compiler keeps one map entry per original wire, even when no replacement gate is emitted. Therefore the equality `map.length = n+q` selects the intended original gate index q; skipped emitted gates cannot shift which original gate is forced false. A `none` map entry denotes false, and `emitPair` performs exactly the valid AND/OR simplifications against false. Mapping a killed gate to none does not remove the AND barrier of a surviving nonconstant AND: two surviving operands always emit another AND.

The `Related` invariant simultaneously maintains old/map length equality and the values of every represented wire, including out-of-range reads. `emitPair_optional_prefix` preserves previously mapped values because `Valid` bounds all some-indices. `compileStep_related` correctly separates the forced gate from ordinary AO2 gates; `form_eval` requires both the AND/OR operation restriction and exact binary fan-in. Although the raw `isAnd` helper maps other operations to false, no semantic theorem claims correctness for those operations.

`compileStep_valid` ensures all emitted gates are binary AND/OR gates reading earlier wires. Unchanged map entries remain bounded as the emitted gate list grows. The source circuit's ReadsBack hypothesis is stronger than the semantic proof needs; ignoring it in the fold is harmless because invalid/future reads were false at their evaluation point and map to none.

For a final none-output, `pruned` deliberately uses index `n+compiledGateCount`, one past the last valid wire. The model's getD semantics makes this false. `IsAO2` constrains gates and their reads, not the output index, so this representation is valid under the exact library definition. Some-output values are covered by the relation. Hence `pruned_eval` proves equality with `forcedValues`, and `pruned_ao` proves the declared AO2 property.

The snapshot does not yet prove equality with the original unmodified circuit, strict gate-count reduction, tCount preservation, or the full lower bound. Those are additional obligations, not implicit consequences of the two final lemmas.

Plain helper-format review passed: only Mathlib and PEqualNP.Defs imports at the top, one own nested namespace, defs and lemmas only, no `_root_`, string literals, attributes, options, commands, sorry, native_decide, or added axioms. This partial helper file has no final theorem named PEqualNP.Outside.L_meta_4675 and therefore is not independently submit-ready as a complete proof.

Independent validation compiled a separate audit copy of the exact snapshot and printed axioms for `pruned_eval` and `pruned_ao`. Exit 0. Both use only `[propext, Classical.choice, Quot.sound]`. Full output: `/tmp/oec/pequalnp-pilot-161/pruning-core-independent-audit.log`. The frozen snapshot was not modified.
