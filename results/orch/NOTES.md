# Orchestration notes

Assigned L-meta-2592: Petersen graph edge function, circuit at most 19 gates containing a NOT. Allowed project module: PEqualNP.Defs.

Root alone renews and submits. Strategies: structural_proof, counterexample, lean_route; checker_review installs missing Lean/cache then reviews.

Desk reductions=true but reductions_live=3: reduction capacity may be full. Existing reductions 271, 318, 408 are in upstream.

Read each strategy-specific note for current details. No proof exists yet.

## Confirmed component status

- Last-NOT cut L-meta-8295 already checked; new Structural.lean is an independent re-derivation.
- Binary floor L-meta-4725 already checked; CaseBounds inlines the allowed-dependency proof and derives NOT count at most four.
- Normalization L-meta-7389 already checked.
- Remaining gaps L-meta-8297, L-meta-4727, L-meta-7391 remain conjectural.
- New route: clean live size19 circuits containing a NOT have a read-once input. CaseBounds formalizes this counting; LeanRoute excludes NOT-only use of an essential positive input; structural examines sharing obstruction for AND/OR use.
- SAT searches produce no witness so far; heuristic candidates are not counterexamples. Restricted SAT UNSAT is not the full theorem.
