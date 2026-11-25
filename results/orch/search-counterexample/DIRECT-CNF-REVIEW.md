# Independent direct-CNF implementation review

Approved for the planned search: no encoding or reconstruction blocker found.

Reviewed source SHA256: `23cb341999a69951a4a0911926ba85726bf499d8908e067238f84613453f9a54` (`multi_output_direct_cnf.py`). The mathematical model and its limited UNSAT scope are covered in `MODEL-REVIEW.md`.

- Clause simplification distinguishes Boolean constants from signed integer literals correctly. Conjunction, disjunction, equality and the sequential at-least counter have the expected semantics. An independent test extracted only the CNF class and checked 1,068 fixed-input truth cases, including signed literals, constants, duplicate/complementary operands, zero thresholds and impossible thresholds.
- The include variables encode positive-signature containment. Each operand is the conjunction of all included available wires, and equality constraints enforce its exact positive signature. Requiring a nonempty included set is sound: an empty conjunction would have the full positive signature, contradicting branch incomparability. The unsigned branch ordering is encoded from most significant bit to least significant bit.
- Output clauses require a false containing wire at every relevant negative row. The joint false-OR bound, targetwise negative pruning and first-OR orbit restriction match the previously audited model. The fixed-baseline control intentionally bypasses the first-OR restriction.
- Witness reconstruction uses only positive signatures to recover backward wire lists and evaluates those lists directly. Independently re-evaluating the saved controls passed all 459 output comparisons for the nine-OR, three-output control and all 7,280 comparisons for the 39-OR, 13-output control. Every cap assignment in each input universe was covered, and both branch lists were nonempty.

The triangle eight-OR run timed out after 30 seconds and is not an UNSAT result. A future full 38-OR SAT witness must still be translated and checked in Lean. A full UNSAT result would exclude only the shared line-variable architecture.

Reproducible audit source and complete output are archived alongside this review as `audit_direct_cnf.py`, `direct-cnf-audit.json` and `direct-cnf-audit.log`. The audit uses the existing Z3 Python installation through `PYTHONPATH=/tmp/oec/pequalnp-pilot-62/z3-python`; no package installation was performed.
