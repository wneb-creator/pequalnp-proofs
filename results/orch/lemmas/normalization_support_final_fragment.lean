namespace PEqualNP.Outside.L_meta_3451_aux.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma witness_below : ∀ a b c d : Bool,
    ∀ j < (Two.witness a b c d).gates.length,
      (NestedCover.gateAt (Two.witness a b c d) j).op = GateOp.and →
      ∀ z : Fin 4 → Bool,
        PEqualNP.EdgeOwnership.gateVal 4 (Two.witness a b c d) j z = true →
        circuitFun 4 (Two.witness a b c d) z = true := by
  let _ : DecidableEq GateOp := NestedCover.gateOpDecEq
  decide

lemma canonical_lower (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    (Two.witness (decide (I 0 0)) (decide (I 0 1))
      (decide (I 1 0)) (decide (I 1 1))).size ≤ C.size := by
  rw [Two.witness_size]
  apply Four.lower_bound_with_certificate Four.certificate _ C hm hb
  intro x
  rw [Two.circuit_truth I C sem, Four.target_bits]
  obtain ⟨ha, hb, hc, hd⟩ := Two.code_bits (decide (I 0 0)) (decide (I 0 1))
    (decide (I 1 0)) (decide (I 1 1))
  simp only [ha, hb, hc, hd, Two.truth]

lemma canonical_sem (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] :
    ∀ z : Fin 4 → Bool,
      circuitFun 4 (Two.witness (decide (I 0 0)) (decide (I 0 1))
        (decide (I 1 0)) (decide (I 1 1))) z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  intro z
  rw [(Two.witness_props _ _ _ _).2.2.1, Two.relation_truth]
  simp only [Two.relation_encode I]

lemma normalize_supported {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ep el : Fin 2 ↪ Fin N)
    (support : ∀ p l, I p l → ∃ a b : Fin 2, p = ep a ∧ l = el b)
    (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack (N + N) C)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  let J : Fin 2 → Fin 2 → Prop := fun p l => I (ep p) (el l)
  let A := Restriction.circuit (project ep el) C
  have am : Monotone2 A := Restriction.mono _ C hm
  have ab : NestedCover.ReadsBack 4 A := Restriction.readsBack _ C hb
  have ae := computes_project ep el I support C hm sem
  let W := Two.witness (decide (J 0 0)) (decide (J 0 1))
    (decide (J 1 0)) (decide (J 1 1))
  have wl : W.size ≤ A.size := canonical_lower J A am ab ae
  have wm : Monotone2 W := (Two.witness_props _ _ _ _).1
  have wb : NestedCover.ReadsBack 4 W := (Two.witness_props _ _ _ _).2.1
  have we := canonical_sem J
  let ρ : Fin 4 → Option (Fin (N + N)) := fun i => some (embed ep el i)
  let D := Restriction.circuit ρ W
  have dm : Monotone2 D := Restriction.mono ρ W wm
  have db : NestedCover.ReadsBack (N + N) D := Restriction.readsBack ρ W wb
  have ds : D.size ≤ C.size := by
    change (Restriction.circuit ρ W).size ≤ C.size
    rw [Restriction.size]
    exact wl.trans_eq (Restriction.size (project ep el) C)
  have de : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true :=
    computes_rename ep el I support W wm we
  have below : ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
      ∀ z : Fin (N + N) → Bool, PEqualNP.EdgeOwnership.gateVal (N + N) D j z = true →
        circuitFun (N + N) D z = true := by
    intro j hj hand z hz
    change PEqualNP.EdgeOwnership.gateVal (N + N) (Restriction.circuit ρ W) j z = true at hz
    rw [Restriction.gate_value_at ρ W wm] at hz
    change circuitFun (N + N) (Restriction.circuit ρ W) z = true
    rw [Restriction.eval ρ W wm]
    exact witness_below _ _ _ _ j
      (by simpa only [D, Restriction.circuit, List.length_map] using hj)
      (Restriction.and_origin ρ W j hand) _ hz
  refine ⟨D, dm, db, ds, de, ?_, ?_⟩
  · intro j hj hand p l hn
    apply Bool.eq_false_iff.mpr
    intro hv
    have ho := below j hj hand _ hv
    rw [incidence_nonedge_false N I D de p l hn] at ho
    cases ho
  · intro j hj hand
    constructor
    · intro p
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_point_false N I D de p] at ho
      cases ho
    · intro l
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_line_false N I D de l] at ho
      cases ho

end PEqualNP.Outside.L_meta_3451_aux.Support
