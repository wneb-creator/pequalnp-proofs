# Compact phase-hinted circuit search

Recorded 2026-11-25 for L-meta-9811. No circuit with at most 24 gates and no full UNSAT certificate has been found by these searches.

The two 571-row screens in `dual-screen-k7-p1-fullneg` and `hybrid-screen-k8-p4-fullneg` each returned UNKNOWN after approximately 179 seconds. Their complete solver output and source snapshots are retained. Neither result proves a lower bound.

`compact_hybrid.py` adds `--hint` to the independently reviewed compact encoder. It assigns each selector according to a concrete circuit, propagates deterministic auxiliary values, and writes a signed phase preference vector for the custom `cadical-phase` wrapper. Preferences add neither clauses nor assumptions. The encoding, extraction, gate cost, and exhaustive validation are unchanged. A seed above the gate budget is allowed as a preference; every violated clause is reported.

The two masked seeds are exact 27-gate circuits: eight ANDs, eighteen ORs, and one NOT. Both expose a shared positive OR value and its negation after the first abstract AND. Their selected-wire total is 36, and the explicit expansion cost is 36 - 8 - 1 = 27. All 27 gates are in the output cone. Replacing the NOT output by true still computes the target; replacing it by false creates 274 mismatches. Thus these are phase and topology seeds, not examples of useful negation savings.

`phase-hint-validation.json` records a complete assignment for every one of the 81,796 variables in the 571-row, budget-36 model, satisfying all 324,335 clauses. At the 24-gate budget 33, the seed violates exactly the terminal size bound and no other clause.

`dual-phase-smoke27` is a positive control. The solver returned SAT in 1.25 seconds; the extracted 27-gate circuit matched all 16,384 inputs. This is not a refutation of the posted statement. No `FOUND.json` is emitted for this 27-gate control.

The three helper sources use their recorded scratch import paths. To reproduce the archived commands, restore `compact_hybrid.py`, `compact_budget.py`, and `seed_to_hybrid.py` under `/tmp/oec/pequalnp-pilot-85/counterexample/`, and `andcount_sat.py` under `/tmp/oec/pequalnp-pilot-85/lower_bound/`. Restore the phase solver wrapper from the separately preserved SAT-tool sources. The compact source snapshots and JSON inputs regenerate the omitted CNFs and phase vectors exactly. `command.json` in the smoke directory records its invocation.

The 24-gate hinted search and longer official-encoding run were still active when this checkpoint was created; their incomplete logs are not included here. All completed solver stdout and stderr in this checkpoint are retained in full.
