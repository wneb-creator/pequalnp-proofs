namespace PEqualNP.Outside.L_meta_2590.Semantic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def chargeSet {n : Nat} (C : Circuit) (p : Fin n) : Finset Nat := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    p.val ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs ∨
    ∃ j < k, (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
      p.val ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs ∧
      n + j ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs

lemma chargeSet_restriction {n : Nat} (C : Circuit) (mono : Monotone2 C) (p : Fin n)
    (nonconstant : ∃ x y, circuitFun n C (fix p false x) ≠ circuitFun n C (fix p false y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p false x)) ∧
      D.size + (chargeSet C p).card ≤ C.size := by
  classical
  have bound : ∀ k ∈ chargeSet C p, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  apply restriction_charged C mono p false nonconstant (chargeSet C p) bound
  intro k hk
  have hkBound := bound k hk
  have getK : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkBound]
  rcases (Finset.mem_filter.mp hk).2 with direct | ⟨j, before, op, reads, consumer⟩
  · apply direct_reader_charge C mono p false k hkBound
    rw [getK] at direct
    exact direct
  · have hj : j < C.gates.length := by omega
    have getJ : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    apply and_consumer_charge C mono p j k hj hkBound before
    · rw [getJ] at op
      exact op
    · rw [getJ] at reads
      exact reads
    · rw [getK] at consumer
      exact consumer

lemma chargeSet_card_le_three {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (small : C.size ≤ 19) (p : Fin n)
    (nonconstant : ∃ x y, circuitFun n C (fix p false x) ≠ circuitFun n C (fix p false y))
    (floor : ∀ D : Circuit, Monotone2 D →
      (∀ x, circuitFun n D x = circuitFun n C (fix p false x)) → 16 ≤ D.size) :
    (chargeSet C p).card ≤ 3 := by
  obtain ⟨D, legal, computes, size⟩ := chargeSet_restriction C mono p nonconstant
  have lower := floor D legal computes
  omega

lemma all_drops_card_le_three {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (small : C.size ≤ 19) (p : Fin n)
    (nonconstant : ∃ x y, circuitFun n C (fix p false x) ≠ circuitFun n C (fix p false y))
    (floor : ∀ D : Circuit, Monotone2 D →
      (∀ x, circuitFun n D x = circuitFun n C (fix p false x)) → 16 ≤ D.size) :
    (droppedSet n C.gates (initial p false)).card ≤ 3 := by
  obtain ⟨D, legal, computes, size⟩ := restriction C mono p false nonconstant
  have lower := floor D legal computes
  have count := elim_drop_count n C.gates (initial p false)
  have empty : (initial p false).2.length = 0 := rfl
  rw [empty] at count
  change C.gates.length ≤ 19 at small
  omega

end PEqualNP.Outside.L_meta_2590.Semantic
