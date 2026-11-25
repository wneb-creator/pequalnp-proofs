# L-meta-2448: strongest preserved result and remaining obligation

The posted theorem is unproved. No file in this branch should be submitted as an unconditional proof of L-meta-2448. The current named file is a compiled conditional result, not a refutation or a reduction submission.

## Reusable conditional theorem

`PEqualNP.Outside.L_meta_2448_aux.oneJunkStar.posted_conclusion_of_at_most_one_junk` is the last helper in the named file. For a triangle-free graph with no four-cycle, it takes a supplied circuit C which is AO2, computes exactly the graph edge function, is a public minimum monotone circuit, and has at most one junk AND. It constructs a public minimum circuit with star profile. No singleton-silence, nonempty-graph, or TopForm hypothesis remains in this helper.

The file is an exact copy of `standalone/AtMostOneJunkStandalone.lean`: 9440 lines, 476959 bytes, importing only Mathlib and PEqualNP.Defs. Its complete named build is `build-partial-12.log`. The final helper axiom audit is `standalone/axiom-audit.log`: only propext, Classical.choice, Quot.sound. `checker-partial-12.log` explicitly rejects the absent unconditional main theorem.

Independent reviewers checked all 418 retained declaration bodies and the namespace rewrite against their sources, reproduced the complete file byte-for-byte, and audited statement scope and plain-file rules. The provenance records are under `standalone/`. The preceding 2078-line collection of context-preserving circuit repairs, ownership criteria, and finite witnesses survives as `lemmas/IntegratedRepairs.lean`; its 143 lemmas have a complete axiom audit.

## What is genuinely missing

Multiple interacting dirty ANDs can share OR networks. An equal-size exchange must account for every external reader of the reused wires. Our extraction lemma gives a gate saving of p minus t for a common-literal component with p input gates and t output interfaces. Minimum size implies p <= t; it does not establish the reverse inequality needed to make the exchange nonincreasing. Neither choosing an earliest dirty gate nor a terminal component resolves this.

A mixed OR support with two neighbors of each of two distinct centers has no common graph neighbor under the no-four-cycle assumption. A clean reader must therefore be centreless. This resource lemma is proved in `MixedSupport`/`MixedReader`, but several dirty regions can merge into one centreless reader. Any valid count must also charge intervening AND merges and handle shared OR signals. A distinct-reader injection is false.

## Strategies ruled out, with explicit limitations

The two-disjoint-stars witness has an eight-OR prefix and a three-AND extension. Exhaustive independent Python and C++ programs find no star-profile replacement using at most three added gates while retaining that prefix. The entire function has a five-gate star circuit, so this is only a fixed-prefix obstruction. Both the original witness and its smaller competitor are checked in Lean.

The P4 expression ((a OR c) AND (b OR d)) AND (b OR c) computes ab OR bc OR cd. Both ANDs are essential on all graph edges, yet that edge set is not a star. It uses the minimum two ANDs according to the complete one-AND/free-OR check, but five total gates; a four-gate circuit exists. The Lean artifact checks the concrete identities and failure of total minimality, not the generic free-OR normalization. Adding an OR-count tie-break avoids this particular witness but leaves the shared-context exchange unproved.

## Computational evidence

The reviewed finite archive has 137 files. Small-instance UNSAT claims are about the explicitly documented normalized binary circuit models. Native-time-limit theta and C7 runs are UNKNOWN, not negative proofs. All SAT witnesses were checked on full truth tables.

The separate free-OR archive has fourteen independently reconstructed CNFs, five fully validated SAT models, six UNSAT results and three UNKNOWN results. It addresses bounded AND counts, not total-gate lower bounds. No SAT result is presented as a Lean proof of the posted statement.

## Reproduction and submission

Use the pinned Lean4.36 toolchain and Mathlib cache. Never lake update. Build the named module with lake build PEqualNP.Outside.L_meta_2448 from lean/. Invoke tools/check-lean.mjs against the exact desk statement, with the explicit PEQUALNP_REAL_LAKE and scratch PEQUALNP_HOME used by this environment. The expected checker verdict for this partial is no-theorem.

A future successful proof PR must contain exactly the named Lean file, prove the exact posted statement, and pass the actual checker. Results files are preserved on this pilot branch under the user's explicit early-push instruction; they must not enter a proof PR diff. All three reduction slots were occupied when this lease was assigned.
