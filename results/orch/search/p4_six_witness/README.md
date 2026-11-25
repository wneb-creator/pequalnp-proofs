# Checked six-gate P4 witness

`P4SixWitness.lean` gives an explicit actual `Circuit` with six binary AND/OR gates on four inputs. It computes `uv ∨ uA ∨ vD`, has distinct earlier operands at every gate, and has both formal derivatives zero on the central edge uv (at singleton u in direction v, and singleton v in direction u). Its direct derivative evaluator follows the same product-rule recurrence as the P4 SAT control.

All six stated facts compile using ordinary `decide` in Lean4.36.0. The preserved axiom audit shows only `propext` for four facts and no axioms for the gate-count and distinctness facts. This is the six-gate upper-bound witness matching the independently audited SAT witness; it does not prove the five-gate lower bound, the eight-input double-star lower bound, or L-meta-2602. No claim is made about derivative behavior outside the explicitly defined recurrence.

Build in the repo lean directory with `lake env lean --root /tmp/oec/pequalnp-pilot-64 -o /tmp/oec/pequalnp-pilot-64/P4SixWitness.olean /tmp/oec/pequalnp-pilot-64/P4SixWitness.lean`. The only import is the existing CircuitLowerBounds definitions. This helper namespace and its diagnostics are research artifacts, not a proof PR file for the leased gap.
