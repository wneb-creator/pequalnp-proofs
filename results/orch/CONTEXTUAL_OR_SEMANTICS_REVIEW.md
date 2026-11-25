# Independent ContextualOrSemantics review

Frozen source `results/orch/lemmas/ContextualOrSemantics.lean`: 599 lines, SHA256 `81d240631fd692db25ebe36812a3bb0c114897838d7765f921ba33202c72d044`.

Verdict: PASS. First 490 lines exactly match the previously reviewed ContextualOr component before its namespace terminator. No forbidden syntax or changed imports. Independent Lean rebuild exited 0 with one harmless unnecessarySimpa warning. Axiom audits of compileNode_related and compile_correct use only propext, Classical.choice, Quot.sound. Full output: `contextual-or-semantics-independent-audit.log`.

The new targetStep masks undemanded channels to false and propagates demanded channels by OR. RelatedContexts relates every indexed pair of optional compiled aliases to this target list, including missing-index false defaults. FreeCertificate is expressed only in terms of the raw input alias and target values; it does not mention the compiled circuit, so the proof is not circular. Recursive Certificates follows targetStep, while the compiler fold follows compileNode. The one-step proof first converts the certificate to the already reviewed local hfree premise using the old relation and raw-input preservation, then preserves existing aliases and appends the proved pair. The fold induction threads both validity and the relation correctly.

This is conditional semantics for a supplied node plan and initial relation. It does not construct a graph demand plan or prove that one exists, establish tCount preservation, or identify the masked target fold with an arbitrary original graph circuit. A full-input result requires certificates/initial relation for every input, not merely one supplied assignment.

Independently reran the supplied bounded tests: 90,650 local cases passed, 9,350 cases excluded by the explicit free-alias premise, 1,000 eight-node plans and all 8,000 Boolean assignments passed. Test source matches the stated conditional contracts. Output: `contextual-or-tests-independent.log`. The Lean theorem, rather than those finite tests, proves the generic conditional result.
