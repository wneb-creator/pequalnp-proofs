import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5691_748
    (peel : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      E.Nonempty → (¬ ∃ v : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v) →
      (∀ i k : Fin n, ∀ j l : Fin m, i ≠ k → j ≠ l →
        ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ z : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) C z =
        decide (∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)) →
      ∃ v : Fin (n+m), let S := E.filter fun e => Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
        S.Nonempty ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (n+m) D ∧
          (∀ z : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) D z =
            decide (∃ i j, (i,j) ∈ E \ S ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)) ∧
          D.size + S.card + 1 ≤ C.size)
    (star : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit), E.Nonempty →
      (∃ v : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ z : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) C z =
        decide (∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)) →
      E.card ≤ C.size)
    (compile : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : Finset (Fin (x1 + x2))), (∀ (x6 : Fin x1) (x7 : Fin x2), x3 x6 x7 → Fin.castAdd x2 x6 ∈ x5 ∨ Fin.natAdd x1 x7 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x7.size ≤ (PEqualNP.ReadTwo.incid x3).card + x5.card - (1 : ℕ) ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x1 + x2 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧ x13 ∈ x9 ∧ x14 ∈ x8) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ ∀ x10 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < x1 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x16 := by
  classical
  intro n m rel dec C square legal evalC
  let SquareFree := fun E : Finset (Fin n × Fin m) =>
    ∀ i k : Fin n, ∀ j l : Fin m, i ≠ k → j ≠ l →
      ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)
  let Computes := fun (E : Finset (Fin n × Fin m)) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∀ z : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) D z =
      decide (∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)
  have cover (k : ℕ) : ∀ (E : Finset (Fin n × Fin m)) (D : PEqualNP.CircuitLowerBounds.Circuit),
      D.size = k → SquareFree E → PEqualNP.TopForm.IsAO2 (n+m) D → Computes E D →
      ∃ U : Finset (Fin (n+m)), (∀ e ∈ E, Fin.castAdd m e.1 ∈ U ∨ Fin.natAdd n e.2 ∈ U) ∧
        E.card + U.card ≤ D.size + 1 := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro E D hk hs hl he
      by_cases hE : E.Nonempty
      · by_cases one : ∃ v : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
        · have small := star n m E D hE one hl he
          obtain ⟨v,inc⟩ := one
          exact ⟨{v}, fun e mem => by simpa using inc e mem, by simp only [Finset.card_singleton]; omega⟩
        · obtain ⟨v,hv⟩ := peel n m E D hE one hs hl he
          let S := E.filter fun e => Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
          have le : S ⊆ E := Finset.filter_subset _ _
          have inc {e} (h : e ∈ S) : Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v :=
            (Finset.mem_filter.mp h).2
          obtain ⟨B,lb,eb,price⟩ := hv.2
          have price' : B.size + S.card + 1 ≤ D.size := price
          have less : B.size < k := by omega
          have subs : E \ S ⊆ E := Finset.sdiff_subset
          have sf : SquareFree (E \ S) := by
            intro i k' j l ne1 ne2 h
            exact hs i k' j l ne1 ne2 ⟨subs h.1,subs h.2.1,subs h.2.2.1,subs h.2.2.2⟩
          obtain ⟨U,hU,hcost⟩ := ih B.size less (E \ S) B rfl sf lb eb
          refine ⟨insert v U, ?_, ?_⟩
          · intro e em
            by_cases hit : e ∈ S
            · rcases inc hit with p | q
              · exact Or.inl (Finset.mem_insert.mpr (Or.inl p))
              · exact Or.inr (Finset.mem_insert.mpr (Or.inl q))
            · exact (hU e (Finset.mem_sdiff.mpr ⟨em,hit⟩)).imp
                (Finset.mem_insert_of_mem) (Finset.mem_insert_of_mem)
          · have count := Finset.card_sdiff_of_subset le
            have sle := Finset.card_le_card le
            have ad := Finset.card_insert_le v U
            omega
      · have empty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
        subst E
        exact ⟨∅, by simp, by simp⟩
  let E := PEqualNP.ReadTwo.incid rel
  have edge (i : Fin n) (j : Fin m) : (i,j) ∈ E ↔ rel i j := by
    dsimp only [E]
    delta PEqualNP.ReadTwo.incid
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have sq : SquareFree E := by simpa only [SquareFree,edge] using square
  have ev : Computes E C := by simpa only [Computes,edge] using evalC
  obtain ⟨U,hU,hcost⟩ := cover C.size E C rfl sq legal ev
  have meets (i : Fin n) (j : Fin m) (h : rel i j) : Fin.castAdd m i ∈ U ∨ Fin.natAdd n j ∈ U :=
    hU (i,j) ((edge i j).mpr h)
  obtain ⟨D,L,R,hl,he,price,hL,hR,hand⟩ := compile n m rel U meets
  refine ⟨D,hl,he,?_,?_⟩
  · change E.card + U.card ≤ C.size + 1 at hcost
    change D.size ≤ E.card + U.card - 1 at price
    omega
  · intro j hj op
    obtain ⟨a,b,ab,ra,lb⟩ := hand j hj op
    exact ⟨a,b,L,R,ab,ra,lb,hL,hR⟩
