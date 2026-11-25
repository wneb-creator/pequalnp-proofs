# L-meta-1031 research checkpoint

The posted theorem is not proved or refuted. No proof PR has been opened. This directory preserves checked partial results and explicitly labelled computational investigations on the authorized fork branch.

The completed [C5 certificate](lemmas/cycle_optimum_certificate.lean) proves an exact minimum of seven gates among normalized five-input circuits computing the C5 edge function: at least four OR gates and three binary AND gates, with a matching witness. The complete 1,816-line file compiled successfully; all 102 finite cases were checked by the Lean kernel, and eight transitive axiom audits use only the standard axioms. [Complete validation](cycle-optimum-validation.txt) includes the unchanged source hash and full output. This finite result does not settle the posted statement.

The exact public statement and desk gap metadata are in `statement.txt` and `gap.json`. Three reductions were already live when the lease was assigned, so a fourth reduction is not an available submission route.

The principal remaining step is a global circuit transformation that gives every AND gate nonempty star ownership without increasing minimum size. `lemmas/normal_form.lean` proves the posted conclusion conditional on existence of a semantically sound minimum; that premise is still unproved.

The strongest new structural component is `lemmas/signed_domination.lean`. It proves signed-test replacement constraints, operand witnesses, and exact binary backward-reading normalization for every minimum monotone graph circuit. Local exchange and private-context lemmas establish valid substitutions under their explicit sharing conditions. Boundary certificate lemmas justify checking edge inputs and maximal independent-set inputs.

Validation texts record the checks and complete output for their snapshots. Exact hashes and line counts for all Lean sources are centralized in [MANIFEST.json](MANIFEST.json). Earlier validation checkpoints are historical; the completed C5 check is [cycle-optimum-validation.txt](cycle-optimum-validation.txt). A Lean compilation or helper audit is not an acceptance verdict for the posted theorem.

`NOTES.md` and `TIMELINE.md` are a dated research log; later entries supersede earlier pending statuses. `REVIEW.md` is the initial static review, followed by later compilation and axiom evidence in the validation records.

Sub-agents: checker_review, lean_setup, normal_form, counterexample, graph_ownership, exchange

Further checked general components include [first-OR deletion](lemmas/first_or_delete.lean), a [two-OR graph bound](lemmas/general_or_lower.lean), and a [first-OR literal restriction](lemmas/first_or_reduction.lean) for sound three-OR programs accepting at least five pairs in graphs without four-cycles. Their hypotheses and remaining scope limits are explicit.
