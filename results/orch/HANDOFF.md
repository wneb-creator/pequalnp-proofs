# pequalnp-pilot-60: L-meta-2602

The posted theorem remains unproved. No refutation was found and no proof PR was opened. The fork branch pnp/pilot-60 preserves compiled partial results and complete validation/research records. The exact posted statement is in statement.txt, with its original allowed imports in imports.json; gap.json contains public assignment metadata without lease data.

## Checked Lean results

- The named file lean/PEqualNP/Outside/L_meta_2602.lean currently has4982lines. Its latest lake build passed,5149jobs; complete output is build-partial-11.stdout/.stderr. It deliberately has no final theorem asserting the posted statement.
- A proper65-gate construction computes the full incidence function and satisfies both zero-derivative clauses. This is feasibility at65, not a lower bound or refutation of the posted63–64 exclusion.
- Inactive-gate and residual-gate removal actually reduce circuit size by one, preserve proper distinct earlier inputs, the full function and both zero derivatives. The minimum realization can therefore be chosen with every gate active and essential on a minimal edge. It may have size below63; no unavailable ordinary lower bound is assumed.
- The normalized obstruction combines this minimum with previously checked flat/clean exclusions: every hypothetical size≤64 marked realization has a minimum with nested AND gates and a dirty AND gate.
- Standalone FalseRows/FreeRows/RowBounds certificates connect704 distinct maximal false inputs to AND-coordinate information. They prove at least10ANDs and, conditionally on at most12, unsigned occurrence widths≤4, same-side unions≤6 and cross-nonedge unions≤5. They do not prove13ANDs.
- PointGadget symbolically excludes one fixed signed-word template using three false rows. It does not classify all templates.
- The main construction/normalization theorems and65-gate witness were audited for axioms: only propext, Classical.choice and Quot.sound occur. Complete output is partial-axioms.stdout/.stderr.

## Remaining mathematical obstacle

A global count controlling dirty intermediates is missing. Two local clean-cover potentials were refuted on small C4-free graphs; even every-gate and every-OR-branch essentiality does not make the local cover drop bounded by one per OR. The generalized two-star construction can hide an arbitrarily large later drop behind earlier dirty OR costs. A valid proof needs an amortized count or a stronger theorem that supplies the missing global inequality.

The ordinary-minimum structural inequality in checked1491 and normal form in1501 do not supply a plane≥63/64 theorem: the U* correction and residual-cover deficit remain unbounded. The separate ordinary≤62 exclusion L-meta-2600 was still open. All three live reductions for2602 were already occupied, so a fourth reduction was not submitted.

## Validation and preservation limits

The full original-statement checker was attempted twice and exhausted the8GiB container memory: checkerexit3, verifierexit137, no verdict. Full outputs and cgroup/resource records are in partial4-checker* and partial6-checker*. Every temporary cache relocation was restored exactly. The verifier imports fullMathlib; a dependency audit confirms every pinned cache artifact is required, so deleting supposedly unused cached modules would not be a valid fix. The current source guard rejects the absent final target theorem, as expected for this helper-only artifact.

No accepted-proof cleanup pass applies: the full target/checker never passed. Named-file line counts before/after that skipped pass are4982/4982. Custom Rule/Plan types pass the current source guard but CONTRIBUTING routes custom datatypes to manual review.

Research SAT outcomes and heuristic searches are explicitly distinguished from Lean proofs; UNKNOWN means unfinished or resource-limited. Independently reviewed complete logs, encoders, compressed CNFs and finite countermodels survive in research-support/, and-count-sat/ and the preservation manifests. See the per-snapshot independent reviews for exact hashes.

Two null desk answers preceded the sole lease. Exact message: “no step is free that you have not already looked at and handed back in the last hour (5); new steps are posted through the day, ask again in a few minutes”. The desk was polled with another=1 and hard=1; no other pilot’s lease was used or released.

Sub-agents: checker_review, structural_proof, counterexample, lemma_search, reduction_design, derivative_lemmas.
