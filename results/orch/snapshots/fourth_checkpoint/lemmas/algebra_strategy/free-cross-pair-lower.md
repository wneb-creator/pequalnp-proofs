# Fixed free cross-pair gadget: checked impossibility

The two-row function is `p(c ∨ u1 ∨ u2 ∨ u3) ∨ q(c ∨ v1 ∨ v2 ∨ v3)`.
Even with all nine `ui ∨ vj` supplied as free correlated input wires, eight additional fan-in-two gates cannot compute it. This retires that fixed-feature gadget only, and is not a refutation of L-meta-650. Joint computation of conditional features is outside this theorem.

`FreeCrossPairLower.lean` proves `no_eight_free_cross` for arbitrary `FanInTwo` circuits, so the bound also permits NOT gates. It uses checked project results outside the final gap's allowed imports: `Helpers.Elim`, `Helpers.PermInputs`, and `L102`. It is a research artifact, not the proposed final proof file.

Raw input order in the Lean statement is `[p,q,c,u1,v1,u2,v2,u3,v3]`. The nine appended free features are the row-major cross-OR matrix. For each raw input, there are two encoded assignments differing only in that raw coordinate, with different target values. Therefore every raw input lies in the output's syntactic support. Eight fan-in-two gates allow at most nine distinct input-support wires, leaving no room for any free feature. Relabeling then gives an ordinary eight-gate circuit for the raw function. Four leaf eliminations reduce that to a four-gate circuit for the five-vertex path; checked theorem L102 requires five gates.

Both earlier exact boundary-signature formula DPs (three matching free ORs and all nine free ORs) independently found minimum formula cost nine. Lower_bound's all-nine SAT also returned UNSAT at eight and SAT at nine, with the latter checked on all 512 raw assignments. The Lean proof does not depend on these computations.

Validation: `lake build PEqualNP.MetaComplexity.L102` exited 0, and `lake env lean .../FreeCrossPairLower.lean` exited 0. Complete stdout/stderr is preserved in the adjacent validation logs. No sorry, axiom, native_decide, or new local options are used.
