# Independent review: structural checkpoints

Reviewed UTC: 2026-11-25T14:12:40.167744+00:00
Reviewer: lean_setup
Verdict: PASS for preservation of these partial results. Any combined target requires its own successful build.

- Source: results/orch/lemmas/SingleNot.lean
  SHA256: 9c5c504384adc6a666475823a43779ee5d336a7151c5ce518f4a1bae6a0049c5
  Lines: 192
- Source: /tmp/oec/pequalnp-pilot-103/MassTwo.lean
  SHA256: ed4720817bf0a5aceda64b0b8830e3df6406efdee380f3735322e641f8430ba6
  Lines: 41

SingleNot semantic review:

- The fold model equals library circuit evaluation and preserves input and earlier gate wires. Monotonicity is only claimed for AND/OR gates and equal-length input lists; out-of-range wire reads remain false.
- first_not_output_impossible concerns a circuit whose selected output is exactly the first NOT wire, with an AND/OR-only prefix. It correctly excludes functions false on the all-false input and true on the all-true input. It does not rule out a NOT feeding later gates.
- unique_not_prefix derives an AND/OR-only prefix from legal operations and a total NOT count of one. The selected output is irrelevant to legality/count, so its temporary value zero is harmless.
- and_not_redundant and or_not_redundant correctly use monotonicity of the negated argument and the full/zero endpoint to show that argument is constant. Neither lemma claims a general NOT-elimination theorem.

MassTwo semantic review:

- cost counts a constant projected wire as one; mass is a sum over list occurrences. It is not yet a circuit gate-count potential.
- Two distinct source elements appearing in the list give two units of mass if both projections are constant, even when their projected functions coincide. Distinct source elements guarantee separate list occurrences, so this is valid with repetitions and noninjective projections.
- The noncomputable constant test uses ordinary classical choice/decidability, not an added axiom or an external oracle.

Format and evidence:

- Imports are permitted and all declarations lie inside child namespaces of the permitted module namespace. There are no forbidden commands, placeholders, axioms, root qualifier, strings, attributes, options, custom data types, or exported instance declarations. The local DecidableEq binding in SingleNot does not export an instance.
- Source text contains no apparent credential material. All four supplied compile logs are empty; each exit 0 is reported by its author. This review did not rerun compilation.
- Neither source proves the posted statement. Preserve the explicit partial-only status; a final PR still requires the exact theorem, checker acceptance, and one added Lean file.
