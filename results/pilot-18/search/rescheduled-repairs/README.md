# Rescheduled multi-source repairs with free output

This is a fresh candidate-only family. Existing CNFs, sources, controllers, and
workers remain unchanged. It makes no normal-form or exhaustive-coverage claim.

The two sources are the completed UNKNOWN stochastic results for seeds 134218
and 134219. Independent all-input checks show that their 20 live gates compute
exactly G minus edge (0,9), respectively G minus edge (1,4). Neither is a witness.

For each source, the generator keeps its 20 live gates and substitutes the missing
edge AND for its one unused gate. The replacement is unused by the original
output, so this cannot change that output. It constructs an original-order and
a randomized topological schedule of the live core, then places the unused slot
at indices 0, 10, and 20. Every live gate value and the selected source output are
compared on all 2048 inputs after renumbering. These 12 seed variants preserve
their respective incomplete source functions exactly.

The generic full-suffix CNF has no clean-prefix or forced-junk requirement.
The only new deletion from the reviewed distance-repair construction is its
single source-output selector unit. The output is therefore selected from all
existing wires, without charging that selection to the gate-description edit
budget. Each variant receives K=4 and K=5 formulas, giving 24 cases. All other
distance constraints are unchanged: exact keep flags for operation and canonical
operand selectors, and the reviewed signed exact totalizer.

An early slot changes which newly introduced computation can be shared by later
gates. A final slot, together with unrestricted output, permits a new output
combination without requiring the old source output gate to remain the output.
Different topological schedules change which rewrites fit into a small numbered
edit neighborhood. These are heuristic reasons for diversification; no runtime
improvement has been measured.

Generator: `generate_rescheduled_repairs.py`.
Audit: `audit_rescheduled_repairs.py`.
Family: `rescheduled-family/`.
Review: `rescheduled-review.json` (valid only after the audit completes).

Reproduction in a fresh output directory, from the repository working directory:

```sh
python3 -B /tmp/oec/pequalnp-pilot-18/orch/S02/generate_rescheduled_repairs.py \
  /tmp/oec/pequalnp-pilot-18/orch/S02/rescheduled-family-new \
  --sources /tmp/oec/pequalnp-pilot-18/stochastic-candidate-134218/engine-result.json \
            /tmp/oec/pequalnp-pilot-18/stochastic-candidate-134219/engine-result.json \
  --seed 134222 --budgets 4 5
```

The audit independently checks the scalar rescheduling semantics and rebuilds
each exact CNF from the reviewed parent, one output-pin deletion, and the reviewed
distance gadget. Its positive compatibility controls intentionally give an exact
22-gate circuit the wrong source output FALSE11; a complete model then selects
the actual correct output34 with zero changed gate descriptions. This demonstrates
that output selection is truly free. Restoring the removed unit rejects that
model. Both K0 and K4 controls are passed through the existing full-CNF/all-input
validator and remain explicitly over the posted gate bound. A full byte-identical
reproduction checks the manifests and all generated files.

Any actual SAT model must pass the full CNF/model validator, all2048-input checks,
normalization and a <=21 gate count, and then Lean verification. UNKNOWN and local
UNSAT do not establish global or assigned-shard exhaustion. No search worker is
part of generation or these controls; the orchestrator owns launches and CPU use.
