# Derivative agent final assessment

L-meta-2602 remains unresolved. No64-gate counterexample was found, and no valid global65-gate lower bound was derived. The checked artifacts are reductions and structural lemmas, not the posted theorem or a refutation. The named-file source guard correctly refuses the missing final theorem.

## Checked contributions

- `lemmas/Derivative.lean`: actual-wire derivative recurrence, uniqueness, guarded-path interpretation, and repeated-AND extraction.
- `lemmas/DeadGate.lean`: deletion/renumbering of an unread gate preserves proper distinct earlier inputs, full Boolean semantics and actual derivative witnesses.
- `lemmas/DerivativeSuperFragment.lean`: derivative positivity implies positivity on any input dominating both base and tangent support; hence edge inactivity forces zero marked signatures.
- `lemmas/ClampDerivativeFragment.lean` and `lemmas/ClampShapeFragment.lean`: same-witness transport through the explicit padding compiler and its syntactic properness/source-exclusion facts. Checked together in `lemmas/ClampAux.lean`.
- `lemmas/DerivativeWitnessFragment.lean`: canonical fresh derivative witness construction, checked in `lemmas/DerivativeWitness.lean`; this supports the subsequently checked derivative-domination/essentiality extension authored by lemma_search.

The full compiler now produces a genuinely smaller proper circuit when deleting a gate preserves all positive edge outputs; minimal circuits can therefore be chosen with every gate active and essential on some incidence edge. This still does not force all AND gates to imply the output.

## Remaining mathematical barrier

The clean-circuit65 charge is already established in the accumulated partial, but an arbitrary minimal counterexample may contain dirty ANDs. Activity and even global gate/OR-branch essentiality do not imply a local removable factor. Matching and path examples exhibit essential dirty filtering and repeated marked reads. The proposed clean-cover and clean-meet-connectivity local potentials both admit drops larger than one per OR, including an example with every OR branch globally essential. Consequently no valid local potential inequality presently supplies the required global OR/AND cost.

The most concrete unformalized normalization found here is copying the body of an earlier gate into a globally redundant OR slot. It keeps physical wires distinct, preserves all positive edge outputs, and decreases ordinary/derivative semantics. Original-input aliases need special treatment; unmarked inputs have zero signatures, while the two marked inputs retain the repeated-read obstruction. Even a complete version of this normalization would still need a global counting argument.

## Finite research checks

`small-marked-results.json` records exhaustive complete-truth/derivative searches for small proper circuits. Double-zero minima found: single edge3, two-edge star4, matching4, P4 outer edge5, P4 middle edge6. All upper witnesses were independently checked by scalar evaluation; lower bounds are computational research results, not Lean proofs. These examples constrain stronger conjectures but do not refute the plane statement.

All64 searches are heuristic/bounded negative results, never claimed UNSAT for the target. The continuation finished all165 remaining repairs in327.318seconds with38,047,362 evaluations and no witness; together with the prior143 repairs, all308 candidates in this specific near-circuit family were checked. Exact scope and hashes are in `search64-continuation-summary.json`.

## Preservation paths

Checked-source metadata and complete output: `clamp-aux-validation.txt`, `clamp-aux-check.log`, `derivative-witness-validation.txt`, `derivative-witness-check.log`, `deadgate-validation.txt`, `deadgate-check.log`.

Independent review records: `firstdirty-review.txt`, `combined-frontier-review.txt`, `clamp-values-review.txt`, `clamp-semantic-review.txt`, `clamp-complete-integration-review.txt`, `point-gadget-review.txt`, and `partial6-integration-review.txt`, `partial9-integration-review.txt`, `partial11-integration-review.txt`. The last integration snapshot was4982lines SHA39f5496ce1d2459e5bde0f2b113f1f4fbf4192aa8222ac81b011e562f132a984; it lacks the main theorem.

Research scripts/logs: `search64.py`, `search64_rotations.py`, `search64_anneal.py`, `search64_cgp.py`, `search64_continue.py`; `search64-repair.log`, `search64-rotations.log`, `search64-anneal.log`, `search64-cgp.log`, `search64-continuation.log`; `search64-results.json`, `search64-notes.md`; `small_marked_enum.py`, `small-marked-enum.log`, `small-marked-results.json`, `small-marked-notes.md`; `firstdirty-obstruction.json`, `firstdirty-frontier-obstruction.json`; `derivative.md`.

Frozen at2026-11-25T04:25UTC. No active process remains from this agent. No further edits planned to these artifacts.
