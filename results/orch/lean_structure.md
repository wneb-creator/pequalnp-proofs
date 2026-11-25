# Lean structure investigation

## Semantics

Circuit is a straight-line gate list. Each gate appends one wire. Out-of-range references read false. AND/OR allow arity 0,1,2 under FanInTwo. NOT ignores its second operand and returns true when no operand exists. Output may be an input, prior gate, or an out-of-range false. No inconsistency or evident counterexample arises from those conventions; normalization has already been checked.

## Existing prerequisite proofs

- `L_meta_4725.lean` (about 3,220 lines) proves the exact binary gate floor `15 + notCount C ≤ C.size`. It counts first branch wires; Petersen requires six branch groups, giving at least `10 - 1 + 6 = 15` non-NOT gates. Its same-file proof includes simplification, minimum circuit extraction, first-branch paths, finite Petersen graph computation, and counting.
- `L_meta_7389.lean` (305 lines) proves normalization corresponding to R_meta_2592_408.
- `L_meta_8295.lean` (66 lines) proves the last-NOT cut corresponding to R_meta_2592_318.
- `L_meta_6060.lean` proves the semantic dedup compiler of R_meta_4727_17.
- `L_meta_7227.lean` proves the signed BinaryCircuit compiler of R_meta_4727_53.

The existing-reductions agent confirmed these are checked in the public feed. Duplicating one would not constitute progress.

## Possible routes and limitations

The generic support argument can be strengthened to count unary NOT gates separately: an n-essential-input circuit satisfies n + notCount ≤ size + 1. For Petersen this gives only 9 non-NOT gates, subsumed by L_meta_4725.

The six-branch lower bound is tight as a graph deletion invariant (Petersen vertex cover has size six); merely rerunning its finite mask computation cannot produce 20 gates. A stronger proof must use the gate operations or interactions between branch regions, not only essential-variable support and branching topology.

The remaining hard statements identified so far are 4727 (1–4 NOT exclusion), 6062 (semantic semantic-state lower bound), 7229 (signed circuit lower bound), 7391 (normalized exclusion), 8297 (last-NOT separator). These are alternative forms of the difficult search, rather than missing routine compiler facts.

One-NOT decomposition gives f(x)=M(x,!h(x)) with M monotone and h monotone. Monotonicity of f alone does not justify replacing !h by a constant; no such shortcut has been established. A gate-preserving negation elimination theorem for these quadratic Petersen outputs would settle the target, but must be proved and cannot be assumed.

2026-11-25T13:50:27.424734+00:00 Initial structural route inventory complete. No new Lean lemma yet.

## Restricted sole-NOT investigation

Finite checks (Python truth-table dynamic programming, not Lean certificates): for 2, 3, and 4 variables, every monotone Boolean function was assigned its exact minimum monotone formula cost (constants cost zero). A second shortest-path search allows one negative input leaf, once in the formula; none beats monotone formula cost. A third search allows one NOT of any monotone source formula, once in the context, up to the maximum monotone formula cost minus one; again no savings. Counts of monotone functions were 6,20,168; maximum formula costs 1,4,7. Script/log are in scratch `structure/one_not_formula.py` and `.log`. This concerns formulas, not shared circuits, so does not settle the circuit task.

A tempting constant-replacement claim is false even with NOT fanout one. Put H(x,y,z)=((x OR y) AND z) OR (x AND y), source G=x. Then H(x,y,NOT x)=y is monotone and the NOT-to-output path is unique, but replacing NOT x by zero gives xy, while replacing it by one gives x OR y. Neither equals y. The whole circuit can be simplified, but this needs more than constant substitution.

Sound restricted statement: if source is input i, downstream H is monotone in its extra NOT wire and has no other dependence on i, and x ↦ H(x,NOT xi) is monotone, then H(x,0)=H(x,1) for every x. Compare the target on update(x,i,0) ≤ update(x,i,1), use the no-other-dependence hypothesis to obtain H(x,1) ≤ H(x,0), and use H monotonicity for the reverse. Thus any useful sole NOT of an input must have a positive reconvergent dependence on that input. Draft Lean proof is results/orch/lemmas/structure.lean; not compiled yet.

2026-11-25T13:59:32.252284+00:00 structure.lean checked with lake env lean using three narrow Mathlib imports; corrected Function.update_self theorem name. See scratch structure/lean-build-02.log for complete output.
